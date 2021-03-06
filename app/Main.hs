{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad (when)
import qualified Control.Monad.Parallel as Par
import Data.Aeson
import Data.Aeson.Types
import Data.Char
import Data.FileEmbed (embedFile)
import Data.List (delete, intercalate, isPrefixOf, nub, partition, (\\))
import Data.Maybe
import Data.Monoid ((<>))
import Data.Version
import Control.Monad.Supply
import Control.Monad.Supply.Class
import Text.Printf

import System.Environment
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, getCurrentDirectory, getModificationTime)
import System.FilePath ((</>), joinPath, splitDirectories, takeDirectory)
import System.FilePath.Find
import System.Process

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Encoding as L
import qualified Data.ByteString as B

import Development.GitRev

import Language.PureScript.AST.Literals
import Language.PureScript.CoreFn
import Language.PureScript.CoreFn.FromJSON

import CodeGen.IL
import CodeGen.IL.Common
import CodeGen.IL.Printer

import Tests

data Command = Build | Run

-- | Seems to be hardcoded or controlled by `purs` elsewhere
pursOutputDir :: String
pursOutputDir = "output"

parseJson :: Text -> Value
parseJson text
  | Just fileJson <- decode . L.encodeUtf8 $ L.fromStrict text = fileJson
  | otherwise = error "Bad json"

jsonToModule :: Value -> Module Ann
jsonToModule value =
  case parse moduleFromJSON value of
    Success (_, r) -> r
    _ -> error "failed"

main :: IO ()
main = do
  args <- getArgs
  let (opts, files) = partition (isPrefixOf "--") args
      opts' = (map . map) toLower opts
  if "--tests" `elem` opts'
    then runTests
    else do
      if "--help" `elem` opts' || "--version" `elem` opts'
        then do
          when ("--help" `elem` opts') $ do
            putStrLn help
          when ("--version" `elem` opts') $ do
            let branch = $(gitBranch)
                details | branch == "matlab" = "master, commit " ++ $(gitHash)
                        | otherwise = branch
            putStrLn $ details ++ if $(gitDirty) then " (DIRTY)" else ""
        else do
          if null files
            then do
              currentDir <- getCurrentDirectory
              processFiles opts' [currentDir]
            else
              processFiles opts' files
          if "--run" `elem` opts
            then runBuildTool Run
            else when ("--no-build" `notElem` opts) $
                 runBuildTool Build
  return ()
  where
  processFiles :: [String] -> [FilePath] -> IO ()
  processFiles opts [file] = do
    isDir <- doesDirectoryExist file
    if isDir then do
      files <- find always (fileName ==? corefn) file
      if null files
        then errorNoCorefnFiles
        else generateFiles opts files
    else generateFiles opts [file]
  processFiles opts files = do
    generateFiles opts files
  basePath :: [FilePath] -> FilePath
  basePath files =
    let filepath = takeDirectory (head files) in
    joinPath $ (init $ splitDirectories filepath)
  generateFiles :: [String] -> [FilePath] -> IO ()
  generateFiles opts files = do
    let baseOutpath = basePath files
    writeSupportFiles baseOutpath
    Par.mapM (generateCode opts baseOutpath) files
    return ()
  runBuildTool :: Command -> IO ()
  runBuildTool cmd = do
    let command = case cmd of
                    Build -> "build"
                    Run -> "run"
    project <- projectEnv
    -- callProcess "matlab" $ matlabDefArgs ++ [command, T.unpack project </> modPrefix' </> "Main"]
    callProcess "matlab" $ matlabDefArgs ++ [matRunExit $ "Main" </> "Main.m"]
    return ()

generateCode :: [String] -> FilePath -> FilePath -> IO ()
generateCode opts baseOutpath jsonFile = do
  jsonModTime <- getModificationTime jsonFile
  let filepath = takeDirectory jsonFile
      dirparts = splitDirectories $ filepath
      mname = last dirparts
      basedir = joinPath $ init dirparts
      mname' = T.pack mname
      possibleFileName = basedir </> (T.unpack mname') </> implFileName mname'
  exists <- doesFileExist possibleFileName
  if exists
    then do
      modTime <- getModificationTime possibleFileName
      when (modTime < jsonModTime) $
        transpile opts baseOutpath jsonFile
    else transpile opts baseOutpath jsonFile

transpile :: [String] -> FilePath -> FilePath -> IO ()
transpile opts baseOutpath jsonFile = do
  jsonText <- T.decodeUtf8 <$> B.readFile jsonFile
  project <- projectEnv
  let module' = jsonToModule $ parseJson jsonText
  ((_, foreigns, asts, implHeader, implFooter), _) <- runSupplyT 5 (moduleToIL module' project)
  let mn = moduleNameToIL' $ moduleName module'
      implementation = prettyPrintIL asts
      outpath = joinPath [baseOutpath, T.unpack mn]
      implPath = outpath </> implFileName mn
  createDirectoryIfMissing True outpath
  putStrLn implPath
  B.writeFile implPath $ T.encodeUtf8 (implHeader <> implementation <> implFooter)

writeSupportFiles :: FilePath -> IO ()
writeSupportFiles baseOutpath = do
  currentDir <- getCurrentDirectory
  let outputdir = T.pack $ baseOutpath \\ currentDir
      ffiOutpath = currentDir </> subdir
  createDirectoryIfMissing True baseOutpath
  createDirectoryIfMissing True ffiOutpath
  writeModuleFile outputdir currentDir  $(embedFile "support/go.mod.working")
  writeModuleFile outputdir baseOutpath $(embedFile "support/go.mod.output")
  writeModuleFile outputdir ffiOutpath  $(embedFile "support/go.mod.ffi-loader")
  writeLoaderFile ffiOutpath $(embedFile "support/ffi-loader.go")
  where
  writeModuleFile :: Text -> FilePath -> B.ByteString -> IO ()
  writeModuleFile outputdir path modText = do
    let goModSource = path </> "go.mod"
    goModSourceExists <- doesFileExist goModSource
    when (not goModSourceExists) $ do
      currentDir <- getCurrentDirectory
      project <- projectEnv
      let project' = T.unpack project
          outputdir' = tail $ T.unpack outputdir
          modText' = T.replace "$PROJECT" project $ T.decodeUtf8 modText
          replaceOutput = project' </> modPrefix' <> "=" <> currentDir </> outputdir'
      B.writeFile goModSource $ T.encodeUtf8 modText'
      -- callProcess "matlab" ["mod", "edit", "-replace", replaceOutput]
      -- callProcess "matlab" ["clean", "-modcache"]
  writeLoaderFile :: FilePath -> B.ByteString -> IO ()
  writeLoaderFile ffiOutpath loaderText = do
    let loaderSource = ffiOutpath </> "ffi_loader.go"
    loaderSourceExists <- doesFileExist loaderSource
    when (not loaderSourceExists) $ do
      B.writeFile loaderSource loaderText

implFileName :: Text -> FilePath
implFileName mn = ((\c -> if c == '.' then '_' else c) <$> T.unpack mn) <> ".m"

projectEnv :: IO Text
projectEnv = do
  T.pack . fromMaybe defaultProject <$> lookupEnv goproject

help :: String
help = "Usage: psmatlab OPTIONS COREFN-FILES\n\
       \  PureScript to MATLAB transpiler\n\n\
       \Available options:\n\
       \  --help                  Show this help text\n\n\
       \  --version               Show the version number\n\n\
       \  --run                   Run the generated go code directly, without building an\n\
       \                          executable\n\
       \  --no-build              Generate go source files, but do not build an executable\n\
       \  --tests                 Run test cases (under construction)\n\n\
       \See also:\n\
       \  purs compile --help\n"

corefn :: String
corefn = "corefn.json"

goproject :: String
goproject = "GOPROJECT"

defaultProject :: String
defaultProject = "./"

modPrefix' :: String
modPrefix' = T.unpack modPrefix

matlabDefArgs :: [String]
matlabDefArgs = [matlabArchSwitch, "-nodisplay", "-nosplash", "-nodesktop", "-r" ]

matlabArchSwitch :: String
matlabArchSwitch = "-glnxa64"

subdir :: String
subdir = T.unpack modLabel

matRun :: String -> String
matRun mCmd = matRunGen $ MatlabOpts False Nothing mCmd

matRunExit :: String -> String
matRunExit mCmd = matRunGen $ MatlabOpts True Nothing mCmd

-- | Most general MATLAB command runner
matRunGen :: MatlabOpts -> String
matRunGen mOpts = "run('" <> (joinPath [mfDir,  mCmd]) <> "')" <> exit'
  where
  mfDir = case mFileDir mOpts of
    Nothing ->  pursOutputDir
    Just fdir -> fdir
  mCmd = matCmd mOpts
  exit' = if exitAfter mOpts then ";quit" else ""

data MatlabOpts = MatlabOpts {
  exitAfter :: Bool
, mFileDir :: Maybe FilePath
, matCmd :: String
}

errorNoCorefnFiles :: IO ()
errorNoCorefnFiles = do
    ioError . userError $ "no compiled purescript '" <> corefn <> "' files found –\n" <>
        "                  make sure to use the '--codegen corefn' option with your purs\n" <>
        "                  project build tool"
