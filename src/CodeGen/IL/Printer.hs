-- | Pretty printer for the AST
module CodeGen.IL.Printer
  ( prettyPrintIL
  , prettyPrintIL1
  , prettyPrintILWithSourceMaps
  , interfaceSource
  , implHeaderSource
  , implFooterSource
  , isLiteral
  , modLabel
  , modPrefix
  ) where

import Prelude.Compat

import Control.Arrow ((<+>))
import Control.Monad (forM, mzero)
import Control.Monad.State (StateT, evalStateT, get)
import Control.PatternArrows
import Data.List (filter, (\\))
import qualified Control.Arrow as A

import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.AST (SourceSpan(..))
import Language.PureScript.CoreImp.AST
import Language.PureScript.Comments
import Language.PureScript.Crash
import Language.PureScript.Names (Ident, runIdent)
import Language.PureScript.Pretty.Common
import Language.PureScript.PSString (PSString, decodeString, mkString)

import CodeGen.IL.Common
import CodeGen.IL.Optimizer.TCO (tcoLoop)

import qualified Language.PureScript.Constants as C

-- TODO: switch to classy prelude and remove these

tshow :: Show a => a -> Text
tshow = T.pack . show

-- END switch to classy prelude

-- TODO: make these keywords
psArg :: Text
psArg = "psArg"

matlabAnon :: [Text] -> Text
matlabAnon args = "@(" <> (T.intercalate "," args) <> ")"

anonDef :: Text
anonDef = matlabAnon [psArg]

anonZero :: Text
anonZero = matlabAnon []

matlabNullary :: Text -> Text
matlabNullary name = "function " <> psRetVal 0 <> " = " <> (withPrefix name) <> "()"

matlabFun :: Int -> Text -> [Text] -> Text
matlabFun _ name [] = matlabNullary name
matlabFun iLvl name args = "function " <> psRetVal iLvl <> " = "
  <> (withPrefix name) <> indentLvlTxt iLvl <> "(" <> (T.intercalate "," args) <> ")"

matlabCall :: Int -> Text -> [Text] -> Text
matlabCall iLvl name args = (withPrefix name) <> indentLvlTxt iLvl <>
  "(" <> (T.intercalate "," args) <> ")"


-- TODO (Christoph): Get rid of T.unpack / pack

literals :: (Emit gen) => Pattern PrinterState AST gen
literals = mkPattern' match'
  where
  match' :: (Emit gen) => AST -> StateT PrinterState Maybe gen
  match' il = (addMapping' (getSourceSpan il) <>) <$> match il

  match :: (Emit gen) => AST -> StateT PrinterState Maybe gen
  match (NumericLiteral _ n) = pure $ emit $ T.pack $ either show show n
  match (StringLiteral _ s) = pure $ emit $ stringLiteral s
  match (BooleanLiteral _ True) = pure $ emit "true"
  match (BooleanLiteral _ False) = pure $ emit "false"
  match (ArrayLiteral _ xs) = mconcat <$> sequence
    [ pure . emit $ arrayType <> "{"
    , intercalate (emit ", ") <$> forM xs prettyPrintIL'
    , pure $ emit "}"
    ]
  -- match (ObjectLiteral _ []) = pure $ emit "std::initializer_list<std::pair<const string, boxed>>{}"
  match (ObjectLiteral _ ps) = mconcat <$> sequence
    [ pure . emit $ dictType <> "("
    , withIndent $ do
        ils <- forM ps $ \(key, value) -> do
                  value' <- prettyPrintIL' value
                  pure $ objectPropertyToString key <> value'
        pure $ intercalate (emit ", ") ils
    , pure $ emit ")"
    ]
    where
    objectPropertyToString :: (Emit gen) => PSString -> gen
    objectPropertyToString s = emit $ stringLiteral s <> ", "
  match (Block _ sts) = mconcat <$> sequence
    [ pure $ emit "\n"
    , withIndent $ prettyStatements sts
    , pure $ emit "\n"
    , currentIndent
    , pure $ emit "end"
    ]
  match (Var _ ident) | ident == C.undefined = pure $ emit undefinedName
  match (Var _ ident) = pure $ emit ident
  match (VariableIntroduction _ ident value) = mconcat <$> sequence
    [ pure . emit $ ident
    , maybe (pure mempty) (fmap (emit " = " <>) . prettyPrintIL') value
    , pure $ emit ";"
    ]
  match (Assignment _ target value) = mconcat <$> sequence
    [ prettyPrintIL' target
    , pure $ emit " = "
    , prettyPrintIL' value
    , pure $ emit ";"
    ]
  match (App _ val []) = mconcat <$> sequence
    [ pure $ emit "Run("
    , prettyPrintIL' val
    , pure $ emit ")"
    ]
  match (App _ (StringLiteral _ u) [arg])
    | Just ty <- decodeString u = mconcat <$> sequence
    [ prettyPrintIL' arg
    ]
  match (App _ (Var _ fn) [arg]) | fn == arrayLengthFn = mconcat <$> sequence
    [ pure $ emit fn
    , pure $ emit "("
    , prettyPrintIL' arg
    , pure $ emit ")"
    ]
  match (App _ (Var _ fn) args) | fn == tcoLoop = mconcat <$> sequence
    [ pure $ emit fn
    , pure $ emit "("
    , intercalate (emit ", ") <$> forM args prettyPrintIL'
    , pure $ emit ")"
    ]
  match (App _ (App Nothing (StringLiteral Nothing fnx) [fn@Function{}]) args)
    | Just ftype <- decodeString fnx
    , "Fn" `T.isPrefixOf` ftype = mconcat <$> sequence
    [ prettyPrintIL' fn
    , pure $ emit "("
    , intercalate (emit ", ") <$> forM args prettyPrintIL'
    , pure $ emit ")"
    ]
  match (App _ (App Nothing (StringLiteral Nothing fnx) [fn]) args)
    | Just ftype <- decodeString fnx
    , "Fn" `T.isPrefixOf` ftype = mconcat <$> sequence
    [ prettyPrintIL' fn
    , pure $ emit "("
    , intercalate (emit ", ") <$> forM args prettyPrintIL'
    , pure $ emit ")"
    ]
  match app@(App{})
    | (val, args) <- unApp app []
    , length args > 1
    = mconcat <$> sequence
    [ pure $ emit "Apply(@"
    , pure $ emit $ fst $ T.breakOn "()" $ prettyPrintIL [val]
    , pure $ emit ", "
    , intercalate (emit ", ") <$> forM args prettyPrintIL'
    , pure $ emit ")"
    ]
  match (App _ val args) = mconcat <$> sequence
    [ pure $ emit "Apply(@"
    , pure $ emit $ fst $ T.breakOn "()" $ prettyPrintIL [val]
    , pure $ emit ", "
    , intercalate (emit ", ") <$> forM args prettyPrintIL'
    , pure $ emit ")"
    ]
  match (Function _ (Just name) [] (Block _ [Return _ ret]))
    | isComplexLiteral ret = mconcat <$> sequence
    [ pure $ emit "\n"
    , pure . emit $ initName name <> " Once\n"
    , prettyPrintIL' $ VariableIntroduction Nothing (valueName name) Nothing
    , pure $ emit "\n\n"
    , pure $ emit anonDef
    , pure . emit $ withPrefix name
    , pure . emit $ "()"
    , pure $ emit "\n"
    , withIndent $ do
        indentString <- currentIndent
        pure $ indentString <> (emit $ initName name <> ".Do(" <> anonZero <> "\n") <>
                 indentString <> indentString <> (emit $ valueName name <> " = ")
    , withIndent $ do
        indentLvl <- indentLevel
        case ret of
          Function _ Nothing args body -> mconcat <$> sequence
            [ pure $ emit $ matlabFun indentLvl name args
            , prettyPrintIL' body
            ]
          _ -> do
            prettyPrintIL' ret
    , pure $ emit "\n"
    , withIndent $ do
        indentString <- currentIndent
        pure $ indentString <> (emit $ "})\n" <> valueName name <>"\n")
    , pure $ emit "end\n\n"
    ]
  match (Function _ (Just name) [] ret) = mconcat <$> sequence
    [ pure $ emit $ "function " <> psRetVal 0 <> " = "
    , pure . emit $ withPrefix name
    , pure . emit $ "()"
    , prettyPrintIL' ret
    ]
  match (Function _ _ args ret) = mconcat <$> sequence
    [ withIndent $ do
        indentLvl <- indentLevel
        pure $ emit $ matlabFun indentLvl innerFunTxt args
    , prettyPrintIL' ret
    , withIndent $ do
        indentLvl <- indentLevel
        let indentText = T.replicate (blockIndent * (indentLvl - 1)) " "
        pure $ emit $ "\n" <> indentText <>
          (psRetVal $ indentLvl - 1) <> " = " <> matlabAnon args <> " " <>
          matlabCall indentLvl innerFunTxt args <> ";"
    ]
  match (Indexer _ (Var _ name) (Var _ "")) = mconcat <$> sequence
    [ prettyPrintIL' (Var Nothing $ withPrefix name)
    , pure $ emit "()"
    ]
  match (Indexer _ (Var _ name) val) = mconcat <$> sequence
    [ prettyPrintIL' val
    , pure $ emit "."
    , prettyPrintIL' (Var Nothing $ withPrefix name)
    , pure $ emit "()"
    ]
  match (Indexer _ prop@StringLiteral{} val@ObjectLiteral{}) = mconcat <$> sequence
    [ pure $ emit "getfield("
    , prettyPrintIL' val
    , pure $ emit ", "
    , prettyPrintIL' prop
    , pure $ emit ")"
    ]
  match (Indexer _ prop@StringLiteral{} val) = mconcat <$> sequence
    [ pure $ emit "getfield("
    , prettyPrintIL' val
    , pure $ emit ", "
    , prettyPrintIL' prop
    , pure $ emit ")"
    ]
  match (Indexer _ index val@ArrayLiteral{}) = mconcat <$> sequence
    [ prettyPrintIL' val
    , pure $ emit "["
    , prettyPrintIL' index
    , pure $ emit "]"
    ]
  match (Indexer _ index val) = mconcat <$> sequence
    [ prettyPrintIL' val
    , pure $ emit "["
    , prettyPrintIL' index
    , pure $ emit "]"
    ]
  match (InstanceOf _ val ty) = mconcat <$> sequence
    [ pure $ emit "Contains("
    , prettyPrintIL' val
    , pure $ emit ", "
    , prettyPrintIL' ty
    , pure $ emit ")"
    ]
  match (While _ cond sts) = mconcat <$> sequence
    [ pure $ emit "for "
    , prettyPrintIL' cond
    , pure $ emit " "
    , prettyPrintIL' sts
    ]
  match (For _ ident start end sts) = mconcat <$> sequence
    [ pure $ emit $ "for " <> ident <> " = "
    , prettyPrintIL' start
    , pure $ emit $ "; " <> ident <> " < "
    , prettyPrintIL' end
    , pure $ emit $ "; " <> ident <> "++ "
    , prettyPrintIL' sts
    ]
  match (ForIn _ ident obj sts) = mconcat <$> sequence
    [ pure $ emit $ "for " <> ident <> " in "
    , prettyPrintIL' obj
    , pure $ emit " "
    , prettyPrintIL' sts
    ]
  match (IfElse _ (Binary _ EqualTo cond@Binary{} (BooleanLiteral Nothing True)) thens elses) = mconcat <$> sequence
    [ pure $ emit "if "
    , prettyPrintIL' cond
    , pure $ emit " "
    , prettyPrintIL' thens
    , maybe (pure mempty) (fmap (emit " else " <>) . prettyPrintIL') elses
    ]
  match (IfElse _ (Binary _ EqualTo cond@Binary{} (BooleanLiteral Nothing False)) thens elses) = mconcat <$> sequence
    [ pure $ emit "if !("
    , prettyPrintIL' cond
    , pure $ emit ") "
    , prettyPrintIL' thens
    , maybe (pure mempty) (fmap (emit " else " <>) . prettyPrintIL') elses
    ]
  match (IfElse _ cond thens elses) = mconcat <$> sequence
    [ pure $ emit "if "
    , prettyPrintIL' cond
    , pure $ emit " "
    , prettyPrintIL' thens
    , maybe (pure mempty) (fmap (emit " else " <>) . prettyPrintIL') elses
    ]
  match (Return _ value) = mconcat <$> sequence
    [ case value of
        (Function _ _ _ _) -> prettyPrintIL' value
        _ -> withIndent $ do
          indentLvl <- indentLevel
          mconcat <$> sequence
            [
              pure $ emit $ psRetVal (indentLvl - 1) <> " = "
            , prettyPrintIL' value
            , pure $ emit ";"
            ]
    ]
  match (ReturnNoResult _) = pure . emit $ "" <> undefinedName
  -- match (Throw _ _) = pure mempty
  match (Throw _ value) = mconcat <$> sequence
    [ pure $ emit "panic("
    , prettyPrintIL' value
    , pure $ emit ")"
    ]
  match (Comment _ com il) = mconcat <$> sequence
    [ pure $ emit "\n"
    , mconcat <$> forM com comment
    , prettyPrintIL' il
    ]
  match _ = mzero

  comment :: (Emit gen) => Comment -> StateT PrinterState Maybe gen
  comment (LineComment com) = fmap mconcat $ sequence $
    [ currentIndent
    , pure $ emit "//" <> emit com <> emit "\n"
    ]
  comment (BlockComment com) = fmap mconcat $ sequence $
    [ currentIndent
    , pure $ emit "/**\n"
    ] ++
    map asLine (T.lines com) ++
    [ currentIndent
    , pure $ emit " */\n"
    , currentIndent
    ]
    where
    asLine :: (Emit gen) => Text -> StateT PrinterState Maybe gen
    asLine s = do
      i <- currentIndent
      pure $ i <> emit " * " <> (emit . removeComments) s <> emit "\n"

    removeComments :: Text -> Text
    removeComments t =
      case T.stripPrefix "*/" t of
        Just rest -> removeComments rest
        Nothing -> case T.uncons t of
          Just (x, xs) -> x `T.cons` removeComments xs
          Nothing -> ""

unary' :: (Emit gen) => UnaryOperator -> (AST -> Text) -> Operator PrinterState AST gen
unary' op mkStr = Wrap match (<>)
  where
  match :: (Emit gen) => Pattern PrinterState AST (gen, AST)
  match = mkPattern match'
    where
    match' (Unary _ op' val) | op' == op = Just (emit $ mkStr val, val)
    match' _ = Nothing

unary :: (Emit gen) => UnaryOperator -> Text -> Operator PrinterState AST gen
unary op str = unary' op (const str)

negateOperator :: (Emit gen) => Operator PrinterState AST gen
negateOperator = unary' Negate (\v -> if isNegate v then "- " else "-")
  where
  isNegate (Unary _ Negate _) = True
  isNegate _ = False

binary :: (Emit gen) => BinaryOperator -> Text -> Operator PrinterState AST gen
binary op str = AssocL match (\v1 v2 -> v1 <> emit (" " <> str <> " ") <> v2)
  where
  match :: Pattern PrinterState AST (AST, AST)
  match = mkPattern match'
    where
    match' (Binary _ op' v1 v2) | op' == op = Just (v1, v2)
    match' _ = Nothing

isLiteral :: AST -> Bool
isLiteral Function{} = True
isLiteral NumericLiteral{} = True
isLiteral StringLiteral{} = True
isLiteral BooleanLiteral{} = True
isLiteral ObjectLiteral{} = True
isLiteral ArrayLiteral{} = True
isLiteral _ = False

isComplexLiteral :: AST -> Bool
-- isComplexLiteral Function{} = True
isComplexLiteral ObjectLiteral{} = True
isComplexLiteral ArrayLiteral{} = True
isComplexLiteral _ = False

unApp :: AST -> [AST] -> (AST, [AST])
unApp (App _ val [arg]) args = unApp val (arg : args)
unApp other args = (other, args)

prettyStatements :: (Emit gen) => [AST] -> StateT PrinterState Maybe gen
prettyStatements sts = do
  ils <- forM sts prettyPrintIL'
  indentString <- currentIndent
  pure $ intercalate (emit "\n") $ map (indentString <>) ils

-- | Generate a pretty-printed string representing a collection of C++ expressions at the same indentation level
prettyPrintILWithSourceMaps :: [AST] -> (Text, [SMap])
prettyPrintILWithSourceMaps il =
  let StrPos (_, s, mp) = (fromMaybe (internalError "Incomplete pattern") . flip evalStateT (PrinterState 0) . prettyStatements) il
  in (s, mp)

prettyPrintIL :: [AST] -> Text
prettyPrintIL = maybe (internalError "Incomplete pattern") runPlainString . flip evalStateT (PrinterState 0) . prettyStatements

-- | Generate an indented, pretty-printed string representing a C++ expression
prettyPrintIL' :: (Emit gen) => AST -> StateT PrinterState Maybe gen
prettyPrintIL' = A.runKleisli $ runPattern matchValue
  where
  matchValue :: (Emit gen) => Pattern PrinterState AST gen
  matchValue = buildPrettyPrinter operators (literals <+> fmap parensPos matchValue)
  operators :: (Emit gen) => OperatorTable PrinterState AST gen
  operators =
    OperatorTable [ [ unary New "?" ]
                  , [ unary     Not                  "!"
                    , unary     BitwiseNot           "~"
                    , unary     Positive             "+"
                    , negateOperator ]
                  , [ binary    Multiply             "*"
                    , binary    Divide               "/"
                    , binary    Modulus              "%" ]
                  , [ binary    Add                  "+"
                    , binary    Subtract             "-" ]
                  , [ binary    ShiftLeft            "<<"
                    , binary    ShiftRight           ">>"
                    , binary    ZeroFillShiftRight   ">>>" ]
                  , [ binary    LessThan             "<"
                    , binary    LessThanOrEqualTo    "<="
                    , binary    GreaterThan          ">"
                    , binary    GreaterThanOrEqualTo ">=" ]
                  , [ binary    EqualTo              "=="
                    , binary    NotEqualTo           "!=" ]
                  , [ binary    BitwiseAnd           "&" ]
                  , [ binary    BitwiseXor           "^" ]
                  , [ binary    BitwiseOr            "|" ]
                  , [ binary    And                  "&&" ]
                  , [ binary    Or                   "||" ]
                    ]

prettyPrintIL1 :: AST -> Text
prettyPrintIL1 = maybe (internalError "Incomplete pattern") runPlainString . flip evalStateT (PrinterState 0) . prettyPrintIL'

stringLiteral :: PSString -> Text
stringLiteral pss | Just s <- decodeString pss = stringLiteral' s
  where
  stringLiteral' :: Text -> Text
  stringLiteral' s = "'" <> T.concatMap encodeChar s <> "'"
  encodeChar :: Char -> Text
  encodeChar '\0' = "\\x00"
  encodeChar '\b' = "\\b"
  encodeChar '\t' = "\\t"
  encodeChar '\n' = "\\n"
  encodeChar '\v' = "\\v"
  encodeChar '\f' = "\\f"
  encodeChar '\r' = "\\r"
  encodeChar '"'  = "\\\""
  encodeChar '\\' = "\\\\"
  encodeChar c = T.singleton $ c
stringLiteral _ = "\"\\uFFFD\""

interfaceSource :: Text -> [(Text,Bool)] -> [Ident] -> Text
interfaceSource _ _ _ = ""


implHeaderSource :: Text -> [Text] -> Text -> Text
implHeaderSource mn imports otherPrefix =
  -- TODO: intercalate paths with 'filesep'?
  (if mn == "Main" then cdProjDirTxt  else "") <>
  "addpath(\'" <> runtime <> "\');\n" <>
  "addpath( ...\n" <>
  (T.intercalate ", ...\n" (formatImport <$> imports)) <> ");\n\n" <>
  if mn == "Main" then mainSource else "\n"
  where
  formatImport :: Text -> Text
  formatImport s = "  \'" <> otherPrefix <> "/" <> modPrefix <> "/" <> s <> "\'"
  mainSource :: Text
  mainSource = "\
    \PS__main();\n\
    \"


implFooterSource :: Text -> [Ident] -> Text
implFooterSource mn foreigns =
  "\n\n\n" <>
  (if null foreigns
    then ""
    else ("// Foreign values\n\n" <>
          foreignDict <> " = "<> foreignMod <> "(\"" <> mn <> "\")\n\n" <>
          (T.concat $ (\foreign' ->
                        let name = moduleIdentToIL foreign' in
                        initName name <> " Once\n" <>
                        valueName name <> " " <> "\n\n" <>
                        "function " <>
                        withPrefix name <>
                        "()\n" <>
                        "    " <> initName name <> ".Do(function() {\n" <>
                        "        " <> valueName name <> " = " <>
                                        "Get(" <> foreignDict <> ", " <>
                                            (stringLiteral . mkString $ runIdent foreign') <> ")\n" <>
                        "    })\n" <>
                        "    pure " <> valueName name <> "\n" <>
                        "end\n\n") <$> foreigns)))

foreignMod :: Text
foreignMod = "Foreign"

foreignDict :: Text
foreignDict = "foreign"

modLabel :: Text
modLabel = "purescript-matlab"

modPrefix :: Text
modPrefix = "output"

runtime :: Text
runtime =  "./" <> modLabel <> "/src/Runtime"

initName :: Text -> Text
initName s = "ₒ" <> s

valueName :: Text -> Text
valueName s = "ₐ" <> s

indentLevel :: StateT PrinterState Maybe Int
indentLevel = do
  current <- indent <$> get
  pure $ current `div` blockIndent

indentLvlTxt :: Int -> Text
indentLvlTxt iLvl = if iLvl > 0 then tshow iLvl else ""

psRetVal :: Int -> Text
psRetVal iLvl = "psRetVal" <> indentLvlTxt (iLvl - 1)

innerFunTxt :: Text
innerFunTxt = "nested"

cdProjDirTxt :: Text
cdProjDirTxt = "mFilePath = mfilename ( 'fullpath' );\n\
  \[mFileDir,~,~] = fileparts(mFilePath);\n\
  \projDir = fullfile(mFileDir, '..', '..');\n\
  \disp(projDir);\n\
  \cd(projDir);\n"
