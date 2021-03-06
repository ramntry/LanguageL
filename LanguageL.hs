module Main where

import Control.Exception.Base (assert)
import Control.Monad (mplus)
import Data.Function (on)
import Data.Maybe (mapMaybe)
import Data.List (intercalate, nub)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec (GenParser, (<|>), (<?>), satisfy, many, parse, char, string, try)
import Text.ParserCombinators.Parsec.Combinator (many1)
import Text.ParserCombinators.Parsec.Expr (Operator (..), Assoc (..), buildExpressionParser)
import Data.Char (isAlpha, isDigit, isSpace)
import Control.Applicative ((<$>), (<*>))

import System.IO (stderr, writeFile, hPutStrLn)
import System.Directory (doesFileExist, findExecutable)
import System.Cmd (rawSystem)
import System.Exit (ExitCode (ExitSuccess))
import System.Process (readProcess)

gccCompatibleCompiler :: FilePath
gccCompatibleCompiler = "gcc"

type ErrorHandler a = String -> a

languageLError message = error ("[Language L] " ++ message ++ ".")
internalError message = languageLError ("Internal Error: " ++ message)
expressionError message = languageLError ("Expression Evaluation: " ++ message)
programError message = languageLError ("Program Execution: " ++ message)
stackMachineError message = languageLError ("Stack Machine Operation: " ++ message)
x86InternalError message = languageLError ("Native Compiler Internal Error: " ++ message)

type VarName = String

infixl 8 :*, :/, :%
infixl 7 :+, :-
infix 5 :<, :>, :==, :!=, :<=, :>=
infixr 4 :&&
infixr 3 :||

data Expression = C Integer
                | V VarName

                | Inc VarName
                | Dec VarName

                | Expression :+ Expression
                | Expression :* Expression
                | Expression :- Expression
                | Expression :/ Expression
                | Expression :% Expression

                | Expression :< Expression
                | Expression :> Expression
                | Expression :== Expression
                | Expression :!= Expression
                | Expression :<= Expression
                | Expression :>= Expression

                | Expression :|| Expression
                | Expression :&& Expression
  deriving (Eq)

data Associativity = LeftA | RightA | NonA deriving (Eq)

instance Show Expression where
  show expr = show' expr 0 NonA
    where parenths outerPreced thisPreced outerAssoc thisAssoc this =
            if precedIsLower || wrongAssoc
            then "(" ++ this ++ ")"
            else this
              where precedIsLower = thisPreced < outerPreced
                    wrongAssoc = thisPreced == outerPreced &&
                                 outerAssoc /= NonA && outerAssoc /= thisAssoc

          associativity op | op `elem` ["*", "/", "%", "+", "-"] = LeftA
                           | op `elem` ["&&", "||"] = RightA
                           | op `elem` ["<", ">", "==", "!=", "<=", ">="] = NonA
                           | otherwise = internalError ("Can not find out associativity of binary" ++
                                                        " operator `" ++ op ++ "'")

          showForBinOp thisPreced op e1 e2 outerPreced outerAssoc =
            let s1 = show' e1 thisPreced LeftA
                s2 = show' e2 thisPreced RightA
            in  parenths outerPreced thisPreced outerAssoc (associativity op)
                         (s1 ++ " " ++ op ++ " " ++ s2)

          show' (C n) = \_ _ -> show n
          show' (V x) = \_ _ -> x

          show' (Inc x) = \preced _ -> parenths preced 8 NonA NonA (x ++ "++")
          show' (Dec x) = \preced _ -> parenths preced 8 NonA NonA (x ++ "--")

          show' (e1 :* e2) = showForBinOp 8 "*" e1 e2
          show' (e1 :/ e2) = showForBinOp 8 "/" e1 e2
          show' (e1 :% e2) = showForBinOp 8 "%" e1 e2

          show' (e1 :+ e2) = showForBinOp 7 "+" e1 e2
          show' (e1 :- e2) = showForBinOp 7 "-" e1 e2

          show' (e1 :< e2) = showForBinOp 5 "<" e1 e2
          show' (e1 :> e2) = showForBinOp 5 ">" e1 e2
          show' (e1 :== e2) = showForBinOp 5 "==" e1 e2
          show' (e1 :!= e2) = showForBinOp 5 "!=" e1 e2
          show' (e1 :<= e2) = showForBinOp 5 "<=" e1 e2
          show' (e1 :>= e2) = showForBinOp 5 ">=" e1 e2

          show' (e1 :|| e2) = showForBinOp 4 "||" e1 e2
          show' (e1 :&& e2) = showForBinOp 3 "&&" e1 e2


inc :: Expression -> Expression
inc (V x) = Inc x
inc _ = internalError "Only variable can be incremented"

dec :: Expression -> Expression
dec (V x) = Dec x
dec _ = internalError "Only variable can be decremented"


data State = State { getMap :: Map.Map VarName Integer } deriving (Eq)

type Semantics = State -> (Integer, State)

emptyState :: State
emptyState = State { getMap = Map.empty }

fromEnv :: [(VarName, Integer)] -> State
fromEnv env = emptyState <== env

showEnv :: [(VarName, Integer)] -> String
showEnv env = "[" ++ (intercalate ", " . map showBinding) env ++ "]"
  where showBinding (x, n) = x ++ " = " ++ show n

instance Show State where
  show s = showEnv $ Map.toList (getMap s)


infix 9 .$
infixl 1 <--, <==
infix 2 .=

(.$) :: State -> VarName -> Integer
s .$ x = Map.findWithDefault (expressionError ("Variable `" ++ x ++ "' is not defined")) x (getMap s)

(.=) :: VarName -> Integer -> (VarName, Integer)
(<--) :: State -> (VarName, Integer) -> State
x .= n = (x, n)
s <-- (x, n) = State $ Map.insert x n (getMap s)

(<==) :: State -> [(VarName, Integer)] -> State
(<==) = foldl (<--)


divisor :: Integer -> Integer
divisor 0 = expressionError "Division by zero"
divisor n = n

bool :: ErrorHandler Bool -> Integer -> Bool
bool _ 0 = False
bool _ 1 = True
bool errHandler _ = errHandler "Only 0 and 1 is allowed in a boolean position"

fromBool :: Bool -> Integer
fromBool False = 0
fromBool True = 1

fromBoolOperation :: (Integer -> Integer -> Bool) -> (Integer -> Integer -> Integer)
fromBoolOperation op = \n m -> fromBool (n `op` m)

divOperation :: Integer -> Integer -> Integer
divOperation = \n m -> n `div` divisor m

modOperation :: Integer -> Integer -> Integer
modOperation = \n m -> n `mod` divisor m

disjOperation :: Integer -> Integer -> Bool
disjOperation = (||) `on` bool expressionError

conjOperation :: Integer -> Integer -> Bool
conjOperation = (&&) `on` bool expressionError

semaForBinOp :: (Integer -> Integer -> Integer) -> Expression -> Expression -> Semantics
semaForBinOp op e1 e2 = \s -> let (a1, s1) = sema e1 s
                                  (a2, s2) = sema e2 s1
                              in  (a1 `op` a2, s2)

semaForBoolOp :: (Integer -> Integer -> Bool) -> Expression -> Expression -> Semantics
semaForBoolOp op = semaForBinOp (fromBoolOperation op)

sema :: Expression -> Semantics
sema (C n) = \s -> (n, s)
sema (V x) = \s -> (s.$ x, s)

sema (Inc x) = \s -> (s.$ x, s <-- x .= s.$ x + 1)
sema (Dec x) = \s -> (s.$ x, s <-- x .= s.$ x - 1)

sema (e1 :+ e2) = semaForBinOp (+) e1 e2
sema (e1 :* e2) = semaForBinOp (*) e1 e2
sema (e1 :- e2) = semaForBinOp (-) e1 e2
sema (e1 :/ e2) = semaForBinOp divOperation e1 e2
sema (e1 :% e2) = semaForBinOp modOperation e1 e2

sema (e1 :< e2) = semaForBoolOp (<) e1 e2
sema (e1 :> e2) = semaForBoolOp (>) e1 e2
sema (e1 :== e2) = semaForBoolOp (==) e1 e2
sema (e1 :!= e2) = semaForBoolOp (/=) e1 e2
sema (e1 :<= e2) = semaForBoolOp (<=) e1 e2
sema (e1 :>= e2) = semaForBoolOp (>=) e1 e2

sema (e1 :|| e2) = semaForBoolOp disjOperation e1 e2
sema (e1 :&& e2) = semaForBoolOp conjOperation e1 e2


eval :: [(VarName, Integer)] -> Expression -> Integer
eval env expr = fst $ sema expr (fromEnv env)



infix 2 ::=
infixr 1:.

data Statement = Skip
               | VarName ::= Expression
               | Write Expression
               | Read VarName
               | Statement:. Statement
               | While Expression Statement
               | If Expression Statement Statement
  deriving (Eq)

instance Show Statement where
  show = showStatement 0

indentation size string = replicate size ' ' ++ string
showStatement indent Skip = indentation indent "skip"
showStatement indent (x ::= e) = indentation indent $ x ++ " := " ++ show e
showStatement indent (Write e) = indentation indent $ "write(" ++ show e ++ ")"
showStatement indent (Read x) = indentation indent $ "read(" ++ x ++ ")"

showStatement indent (st1:. st2) = showStatement indent st1 ++ ";\n" ++
                                   showStatement indent st2

showStatement indent (While e st) = indentation indent ("while " ++ show e ++ " do\n") ++
                                    showStatement (indent + 2) st

showStatement indent (If e st1 st2) = indentation indent ("if " ++ show e ++ " then\n") ++
                                        showStatement (indent + 2) st1 ++ "\n" ++
                                      indentation indent "else\n" ++
                                        showStatement (indent + 2) st2

showProgram :: Statement -> String
showProgram = unlines . map ("| " ++) . lines . show


type Stream = [Integer]
type Configuration = (State, Stream, Stream)
type ProgramSema = Statement -> Stream -> Stream

emptyInputStreamMessage :: String
emptyInputStreamMessage = "Can not read from an empty input stream"

nonEmptyInputStreamMessage :: String
nonEmptyInputStreamMessage = "Program has completed with non-empty input stream"

bigStep :: Statement -> Configuration -> Configuration
bigStep Skip conf = conf

bigStep (x ::= e) (s, i, o) =
  let (a, s1) = sema e s
      s2 = s1 <-- x .= a
  in  (s2, i, o)

bigStep (Write e) (s, i, o) =
  let (a, s1) = sema e s
  in  (s1, i, a : o)

bigStep (Read x) (s, a : i, o) = (s <-- x .= a, i, o)
bigStep (st1:. st2) conf = (bigStep st2 . bigStep st1) conf

bigStep loop@(While e st) (s, i, o) =
  let (a, s1) = sema e s
  in  if bool programError a
      then (bigStep loop . bigStep st) (s1, i, o)
      else (s1, i, o)

bigStep (If e st1 st2) (s, i, o) =
  let (a, s1) = sema e s
  in  if bool programError a
      then bigStep st1 (s1, i, o)
      else bigStep st2 (s1, i, o)

bigStep _ _ = programError emptyInputStreamMessage


initialConf :: Stream -> Configuration
initialConf input = (emptyState, input, [])

programSema :: ProgramSema
programSema statement input = case bigStep statement (initialConf input) of
                                (s, [], output) -> forseState s $ reverse output
                                _ -> programError nonEmptyInputStreamMessage
  where forseState = seq . length . show


data SmallStepResult = Completed Configuration
                     | Uncompleted Configuration Statement

instance Show SmallStepResult where
  show (Completed conf) = show conf ++ " ==|"
  show (Uncompleted conf continuation) = show conf ++ " =>>\n" ++ show continuation


infixl 1 |>

(|>) :: a -> (a -> b) -> b
arg |> func = func arg


smallStep :: Statement -> Configuration -> SmallStepResult
smallStep Skip conf = Completed conf
smallStep st@(_ ::= _) conf = Completed $ bigStep st conf
smallStep st@(Write _) conf = Completed $ bigStep st conf
smallStep st@(Read _) conf = Completed $ bigStep st conf

smallStep (st1:. st2) conf =
  case smallStep st1 conf of
    Completed conf1 -> Uncompleted conf1 st2
    Uncompleted conf1 st1' -> Uncompleted conf1 (st1':. st2)

smallStep loop@(While e st) conf = Uncompleted conf $ If e (st:. loop) Skip

smallStep (If e st1 st2) (s, i, o) =
  let (a, s1) = sema e s
  in  if bool programError a
      then Uncompleted (s1, i, o) st1
      else Uncompleted (s1, i, o) st2


step :: SmallStepResult -> SmallStepResult
step result@(Completed _) = result
step (Uncompleted conf continuation) = smallStep continuation conf

step0 :: Statement -> Stream -> SmallStepResult
step0 program input = Uncompleted (initialConf input) program

isCompleted :: SmallStepResult -> Bool
isCompleted (Completed _) = True
isCompleted _ = False


data ExecutionHistory = ExecutionHistory [SmallStepResult] SmallStepResult

instance Show ExecutionHistory where
  show (ExecutionHistory uncompletedSteps completedStep) =
    uncompletedSteps ++ [completedStep]
    |> map show
    |> zipWith (\n res -> n ++ ": " ++ res) (map show [0..])
    |> intercalate "\n\n"

configurationOfHistory :: ExecutionHistory -> Configuration
configurationOfHistory (ExecutionHistory _ (Completed conf)) = conf
configurationOfHistory _ =
  internalError "Last small step in execution history must return completed result"

stepByStep :: Statement -> Stream -> ExecutionHistory
stepByStep program input =
  let (uncompletedSteps, completedStep : _) =
        step0 program input
        |> iterate step
        |> break isCompleted
  in  ExecutionHistory uncompletedSteps completedStep


checkExpression :: Expression -> [(VarName, Integer)] -> Integer -> String
checkExpression expr env expected = assert (actual == expected) $
  "Expression '" ++ show expr ++ "' in state " ++ showEnv env ++
  " was evaluated with the result " ++ show actual ++
  " while " ++ show expected ++ " was expected."
    where actual = eval env expr

test1Expr = Inc "x" :* V "y" :+ V "x"
test1Env = [("x", 10), ("y", 20)]
test1Expected = 211
test1Checked = checkExpression test1Expr test1Env test1Expected

test2Expr = C 20 :< C 10 :|| Inc "x" :== V "y" :- V "x" :|| V "z"
test2Env = [("x", 0), ("y", 1)]
test2Expected = 1
test2Checked = checkExpression test2Expr test2Env test2Expected


checkProgram :: ProgramSema -> Statement -> Stream -> Stream -> String
checkProgram pSema program input expected = assert (actual == expected) $
  "The program below has completed execution on an input stream " ++ showStream input ++
  " with output stream " ++ showStream actual ++
  " while expected output is " ++ showStream expected ++ ".\n" ++
  showProgram program ++ "\n"
    where actual = pSema program input
          showStream = intercalate " " . map show

checkHistory :: Statement -> Stream -> Configuration -> String
checkHistory program input expected = assert (actual == expected) $
  "Execution history: (expected configuration is " ++ show expected ++ ")" ++
  "\n\n" ++ show history ++ "\n"
    where history = stepByStep program input
          actual = configurationOfHistory history


programOfExpression :: [(VarName, Integer)] -> Expression -> Statement
programOfExpression env expr =
  foldr (\(x, n) acc -> x ::= C n:. acc) (Write (expr)) env


-- Factorial
testProgram1 :: Statement
testProgram1 =
  Read "n":.
  If (V "n" :< C 0) (
    Write (C 0))
  (
    "x" ::= C 1:.
    "i" ::= C 0:.
    While (Inc "i" :< V "n") (
      "x" ::= V "x" :* V "i"):.
    Write (V "x"))

-- GCD (Euclid)
testProgram2 =
  Read "a":.
  Read "b":.
  While (V "b" :!= C 0 :&& V "a" :!= C 0) (
      "a" ::= V "a" :% V "b":.
      If (V "a" :!= C 0) (
        "b" ::= V "b" :% V "a")
      (
        Skip)):.
  Write (V "a" :+ V "b")

-- Fibonacci Sequence
testProgram3 =
  Read "n":.
  "curr" ::= C 1:.
  "next" ::= C 1:.
  While (Dec "n" :!= C 0) (
    Write (V "curr"):.
    "tmp" ::= V "next":.
    "next" ::= V "curr" :+ V "next":.
    "curr" ::= V "tmp")

-- Snake (Spiral traverse of 2D integral plane)
testProgram6 =
  Read "n":.
  "x" ::= C 0:.
  "y" ::= C 0:.
  "n" ::= V "n" :- C 1:.
  While (V "n" :> C 0) (
    "k" ::= Dec "n":.
    "i" ::= V "k":.
    While (Dec "i" :> C 0) (
      Write (V "y"):.
      Write (Inc "x")):.
    "i" ::= V "k":.
    While (Dec "i" :> C 0) (
      Write (Inc "y"):.
      Write (V "x")):.
    "i" ::= V "k":.
    While (Dec "i" :> C 0) (
      Write (V "y"):.
      Write (Dec "x")):.
    "i" ::= V "n":.
    While (Dec "i" :> C 0) (
      Write (Dec "y"):.
      Write (V "x")):.
    Write (V "y"):.
    Write (Inc "x"):.
    "n" ::= V "n" :- C 1):.
  If (V "n" :== C 0) (
    Write (V "y"):.
    Write (V "x"))
  (
    Skip)


type NameGenerator = VarName -> VarName
type ListMacro = (VarName, VarName)

isNotPrimeMacro :: NameGenerator -> VarName -> VarName -> Statement
isNotPrimeMacro name number result = let divider = name "divider" in
  result ::= C 0:.
  divider ::= C 2:.
  While (V divider :* V divider :<= V number :&& C 1 :- V result) (
    If (V number :% V divider :== C 0) (
      result ::= C 1)
    (
      divider ::= V divider :+ C 1))

powerMacro :: NameGenerator -> VarName -> VarName -> Statement
powerMacro name x power = let acc = name "acc" in
  acc ::= C 1:.
  While (V power :> C 0) (
    If (V power :% C 2) (
      acc ::= V acc :* V x)
    (
      Skip):.
    x ::= V x :* V x:.
    power ::= V power :/ C 2):.
  x ::= V acc

factorOutMacro :: VarName -> VarName -> VarName -> Statement
factorOutMacro prime x power =
  power ::= C 0:.
  While (V x :% V prime :== C 0) (
    power ::= V power :+ C 1:.
    x ::= V x :/ V prime)

emptyListMacro :: ListMacro -> Statement
emptyListMacro (list, lastPrime) =
  list ::= C 1:.
  lastPrime ::= C 1

pushMacro :: NameGenerator -> ListMacro -> VarName -> Statement
pushMacro name (list, lastPrime) item = let notFoundYet = name "not_found_yet"
                                            factor = name "factor" in
  notFoundYet ::= C 1:.
  While (V notFoundYet) (
    lastPrime ::= V lastPrime :+ C 1:.
    isNotPrimeMacro name lastPrime notFoundYet):.
  factor ::= V lastPrime:.
  powerMacro name factor item:.
  list ::= V list :* V factor

popMacro :: NameGenerator -> ListMacro -> VarName -> Statement
popMacro name (list, lastPrime) result = let notFoundYet = name "not_found_yet" in
  factorOutMacro lastPrime list result:.
  notFoundYet ::= C 1:.
  While (V notFoundYet) (
    lastPrime ::= V lastPrime :- C 1:.
    isNotPrimeMacro name lastPrime notFoundYet)

-- List Reverse
testProgram7 = let list = ("list", "last_prime") in
  Read "n":.
  emptyListMacro list:.
  "i" ::= V "n":.
  While (Dec "i" :> C 0) (
    Read "x":.
    pushMacro id list "x"):.
  Write (V "n"):.
  "i" ::= V "n":.
  While (Dec "i" :> C 0) (
    popMacro id list "x":.
    Write (V "x"))


checkedProgram1 :: String
checkedProgram1 = checkProgram programSema testProgram1 [6] [720]

checkedProgram7 :: String
checkedProgram7 = checkProgram compiledProgramSema testProgram7 (len : testList) (len : reverse testList)
  where testList = [2, 15, 3, 0, 9, 6, 4, 11, 2, 5, 7, 2, 1, 0, 0, 1]
        len = fromIntegral $ length testList

checkedHistory1 :: String
checkedHistory1 = checkHistory testProgram1 [2]
  (emptyState <-- "x" .= 2
              <-- "i" .= 3
              <-- "n" .= 2, [], [2])

checkedHistory2 :: String
checkedHistory2 = checkHistory testProgram2 [75600, 12375]
  (emptyState <-- "a" .= 0
              <-- "b" .= 225, [], [225])

checkedHistory3 :: String
checkedHistory3 = checkHistory testProgram3 [5]
  (emptyState <-- "curr" .= 8
              <-- "next" .= 13
              <-- "tmp" .= 8
              <-- "n" .= -1, [], reverse [1, 1, 2, 3, 5])



type Parser st a = GenParser Char st a

variable :: Parser st Expression
variable = do
  hd <- nameHead
  tl <- nameTail
  return (V (hd : tl))
    where nameHead = satisfy $ (||) <$> isAlpha <*> (`elem` "_$")
          nameTail = many $ nameHead <|> satisfy isDigit

constant :: Parser st Expression
constant = do
  digits <- many1 $ satisfy isDigit
  return (C (read digits))

operatorTable :: [[Operator Char st Expression]]
operatorTable = [ [postfix "++" inc, postfix "--" dec]
                , binaryLeft [("*", (:*)), ("/", (:/)), ("%", (:%))]
                , binaryLeft [("+", (:+)), ("-", (:-))]
                , binaryNone [("<", (:<)), (">", (:>)), ("==", (:==)), ("!=", (:!=)), ("<=", (:<=)), (">=", (:>=))]
                , [binary AssocRight "&&" (:&&)]
                , [binary AssocRight "||" (:||)]
                ]
  where postfix literal op = Postfix (try (string literal) >> return op)
        binary assoc literal op = Infix (try (string literal) >> return op) assoc
        binaryLeft = map (uncurry (binary AssocLeft))
        binaryNone = map (uncurry (binary AssocNone))

term :: Parser st Expression
term = variable
   <|> constant
   <|> (do char '('
           expr <- expression
           char ')'
           return expr)
   <?> "expression"

expression :: Parser st Expression
expression = buildExpressionParser operatorTable term

parseExpression :: String -> Expression
parseExpression input =
  case parse expression "" (filter (not . isSpace) input) of
    Right expr -> expr
    Left message -> internalError ("Expression parsing error: " ++ show message)

test1Parsing :: String
test1Parsing = assert (parseExpression (show test1Expr) == test1Expr) "Parsing 1: OK"

test2Parsing :: String
test2Parsing = assert (parseExpression (show test2Expr) == test2Expr) "Parsing 2: OK"


type Addr = Int

data Instruction = E                  -- End
                 | R                  -- Read
                 | W                  -- Write
                 | I Integer          -- Const (Immediate)
                 | L VarName          -- Load
                 | S VarName          -- Store
                 | B BinaryOperator   -- BinOp
                 | J Addr             -- Jump
                 | JT Addr            -- Jump If True
                 | JF Addr            -- Jump If False

data BinaryOperator = Add | Sub | Mul | Div | Mod
                    | Lt | Gt | Eq | Neq | Le | Ge
                    | Disj | Conj

instance Show BinaryOperator where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Mod = "%"

  show Lt = "<"
  show Gt = ">"
  show Eq = "=="
  show Neq = "!="
  show Le = "<="
  show Ge = ">="

  show Disj = "||"
  show Conj = "&&"

instance Show Instruction where
  show E = "End"
  show R = "Read"
  show W = "Write"
  show (I n) = "Const " ++ show n
  show (L x) = "Load " ++ x
  show (S x) = "Store " ++ x
  show (B op) = "( " ++ show op ++ " )"
  show (J addr) = "Jump :" ++ show addr
  show (JT addr) = "JumpIf1 :" ++ show addr
  show (JF addr) = "JumpIf0 :" ++ show addr


binOperation :: BinaryOperator -> (Integer -> Integer -> Integer)
binOperation Add = (+)
binOperation Sub = (-)
binOperation Mul = (*)
binOperation Div = divOperation
binOperation Mod = modOperation

binOperation Lt = fromBoolOperation (<)
binOperation Gt = fromBoolOperation (>)
binOperation Eq = fromBoolOperation (==)
binOperation Neq = fromBoolOperation (/=)
binOperation Le = fromBoolOperation (<=)
binOperation Ge = fromBoolOperation (>=)

binOperation Disj = fromBoolOperation disjOperation
binOperation Conj = fromBoolOperation conjOperation


type SMInstructions = [Instruction]
type Stack = [Integer]
type SMConfiguration = (Stack, State, Stream, Stream)

goto :: SMInstructions -> Addr -> SMInstructions
goto program addr | addr > length program = stackMachineError ("Can not jump to instruction with address "
                                                            ++ show addr ++ ", the program have "
                                                            ++ show (length program) ++ " instructions only")
                  | otherwise = drop addr program


stackUnderflowMessage :: String -> String
stackUnderflowMessage instructionInfo = "Stack Underflow (" ++ instructionInfo ++ ")"

runMachine :: SMInstructions -> SMInstructions -> SMConfiguration -> SMConfiguration
runMachine _ (E : _) conf = conf

runMachine program (R : instrs) (s, m, z : i, o) = runMachine program instrs (z : s, m, i, o)
runMachine _ (R : _) (_, _, [], _) = stackMachineError emptyInputStreamMessage

runMachine program (W : instrs) (z : s, m, i, o) = runMachine program instrs (s, m, i, z : o)
runMachine _ (W : _) ([], _, _, _) = stackMachineError (stackUnderflowMessage "Write")

runMachine program (I n : instrs) (s, m, i, o) = runMachine program instrs (n : s, m, i, o)
runMachine program (L x : instrs) (s, m, i, o) = runMachine program instrs ((m.$ x) : s, m, i, o)

runMachine program (S x : instrs) (z : s, m, i, o) = runMachine program instrs (s, m <-- x .= z, i, o)
runMachine _ (S x : _) ([], _, _, _) = stackMachineError (stackUnderflowMessage $ "Store " ++ x)

runMachine program (B op : instrs) (b : a : s, m, i, o) = runMachine program instrs (binOperation op a b : s, m, i, o)
runMachine _ (B op : _) _ = stackMachineError (stackUnderflowMessage $ "BinOp " ++ show op)

runMachine program (J addr : _) conf = runMachine program (program `goto` addr) conf

runMachine program (JT addr : _) (1 : s, m, i, o) = runMachine program (program `goto` addr) (s, m, i, o)
runMachine program (JT _ : instrs) (0 : s, m, i, o) = runMachine program instrs (s, m, i, o)
runMachine program (JT _ : _) ([], _, _, _) = stackMachineError (stackUnderflowMessage "Jump If True")

runMachine program (JF addr : _) (0 : s, m, i, o) = runMachine program (program `goto` addr) (s, m, i, o)
runMachine program (JF _ : instrs) (1 : s, m, i, o) = runMachine program instrs (s, m, i, o)
runMachine program (JF _ : _) ([], _, _, _) = stackMachineError (stackUnderflowMessage "Jump If False")

runMachine _ [] _ = stackMachineError "Unexpected end of program"


machineSema :: SMInstructions -> Stream -> Stream
machineSema instrs i | (_, _, [], o) <- runMachine instrs instrs ([], emptyState, i, []) = reverse o
                     | otherwise = stackMachineError nonEmptyInputStreamMessage


testMachineInstrs :: SMInstructions
testMachineInstrs =
  [ R      --  0
  , S "i"  --  1
  , J 9    --  2
  , L "i"  --  3
  , W      --  4
  , L "i"  --  5
  , I 1    --  6
  , B Sub  --  7
  , S "i"  --  8
  , I 0    --  9
  , L "i"  -- 10
  , B Lt   -- 11
  , JT 3   -- 12
  , E      -- 13
  ]

testMachineInput :: Integer
testMachineInput = 20

testMachineExpected :: Stream
testMachineExpected = reverse [1 .. testMachineInput]

testMachineActual :: Stream
testMachineActual = machineSema testMachineInstrs [testMachineInput]

testMachineChecked :: String
testMachineChecked = assert (testMachineActual == testMachineExpected) "testMachine: OK"


compileBinOp :: BinaryOperator -> Expression -> Expression -> SMInstructions
compileBinOp op e1 e2 = compileExpression e1 ++ compileExpression e2 ++ [B op]

compileExpression :: Expression -> SMInstructions
compileExpression (V x) = [L x]
compileExpression (C n) = [I n]

compileExpression (Inc x) = [L x, L x, I 1, B Add, S x]
compileExpression (Dec x) = [L x, L x, I 1, B Sub, S x]

compileExpression (e1 :+ e2) = compileBinOp Add e1 e2
compileExpression (e1 :* e2) = compileBinOp Mul e1 e2
compileExpression (e1 :- e2) = compileBinOp Sub e1 e2
compileExpression (e1 :/ e2) = compileBinOp Div e1 e2
compileExpression (e1 :% e2) = compileBinOp Mod e1 e2

compileExpression (e1 :< e2) = compileBinOp Lt e1 e2
compileExpression (e1 :> e2) = compileBinOp Gt e1 e2
compileExpression (e1 :== e2) = compileBinOp Eq e1 e2
compileExpression (e1 :!= e2) = compileBinOp Neq e1 e2
compileExpression (e1 :<= e2) = compileBinOp Le e1 e2
compileExpression (e1 :>= e2) = compileBinOp Ge e1 e2

compileExpression (e1 :|| e2) = compileBinOp Disj e1 e2
compileExpression (e1 :&& e2) = compileBinOp Conj e1 e2


compileEnv :: [(VarName, Integer)] -> SMInstructions
compileEnv = concatMap (\(x, n) -> [I n, S x])

machineExpressionValue :: [(VarName, Integer)] -> Expression -> Integer
machineExpressionValue env e | ([value], _, [], []) <- runMachine instrs instrs ([], emptyState, [], []) = value
                             | otherwise = stackMachineError "machineExpressionValue"
  where instrs = compileEnv env ++ compileExpression e ++ [E]


testMachineExpressionValue1 =
  assert (machineExpressionValue test1Env test1Expr == test1Expected) "testMachineExpressionValue1: OK"

testMachineExpressionValue2 =
  assert (machineExpressionValue test2Env test2Expr == test2Expected) "testMachineExpressionValue2: OK"


compileStatement :: Addr -> Statement -> SMInstructions
compileStatement _ Skip = []
compileStatement _ (x ::= e) = compileExpression e ++ [S x]
compileStatement _ (Read x) = [R, S x]
compileStatement _ (Write e) = compileExpression e ++ [W]

compileStatement n (st1:. st2) = let st1' = compileStatement n st1
                                     st2' = compileStatement (n + length st1') st2
                                 in  st1' ++ st2'

compileStatement n (While e st) = let l = n + 1
                                      st' = compileStatement l st
                                      l0 = l + length st'
                                  in  [J l0] ++ st' ++ compileExpression e ++ [JT l]

compileStatement n (If e st1 st2) = let e' = compileExpression e
                                        f = n + length e' + 1
                                        st1' = compileStatement f st1
                                        l1 = f + length st1' + 1
                                        st2' = compileStatement l1 st2
                                        l2 = l1 + length st2'
                                    in  e' ++ [JF l1] ++ st1' ++ [J l2] ++ st2'


newtype SMProgram = SMProgram { getInstructions :: SMInstructions }

ljust :: Int -> String -> String
ljust width string = string ++ replicate (width - length string) ' '

rjust :: Int -> String -> String
rjust width string = replicate (width - length string) ' ' ++ string

instance Show SMProgram where
  show (SMProgram instructions) = concatMap showLine $ zip [0..] instructions
    where showLine (addr, instr) = rjust maxLen addr' ++ ":   " ++ show instr ++ "\n"
            where addr' = show addr
          maxLen = length (show (length instructions - 1))


compileProgram :: Statement -> SMProgram
compileProgram program = SMProgram $ compileStatement 0 program ++ [E]


compiledProgramSema :: Statement -> Stream -> Stream
compiledProgramSema = machineSema . getInstructions . compileProgram



checkedCompiledProgram1 = checkProgram compiledProgramSema testProgram1 [6] [720]
checkedCompiledProgram2 = checkProgram compiledProgramSema testProgram2 [75600, 12375] [225]
checkedCompiledProgram3 = checkProgram compiledProgramSema testProgram3 [10] [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]



type Symbol = String

data X86Reg = Rax | Rcx | Rbx | Rdx | Rdi | Rsp | Rbl | R12 | R13 | R14 | R15
  deriving (Eq)

data X86Operand = Register X86Reg
                | Symbol Symbol
                | Immediate Int
                | Indirect X86Reg
  deriving (Eq)

data X86Label = Local Addr
              | Global Symbol
  deriving (Eq, Ord)

data X86Condition = IfE
                  | IfNe
                  | IfZ
                  | IfNz
                  | IfL
                  | IfG
                  | IfLe
                  | IfGe


data X86Instruction = Xor X86Operand X86Operand
                    | Or X86Operand X86Operand
                    | And X86Operand X86Operand
                    | XAdd X86Operand X86Operand
                    | XSub X86Operand X86Operand
                    | Imul X86Operand
                    | Cqo
                    | Idiv X86Operand
                    | Mov X86Operand X86Operand
                    | Cmp X86Operand X86Operand
                    | SetCond X86Condition X86Operand
                    | JmpCond X86Condition X86Label
                    | Jmp X86Label
                    | Call X86Label
                    | Push X86Operand
                    | Pop X86Operand
                    | Nop

jumpTarget :: X86Instruction -> Maybe X86Label
jumpTarget (JmpCond _ label) = Just label
jumpTarget (Jmp label) = Just label
jumpTarget _ = Nothing


data X86Line = X86Line { getLabel :: Maybe X86Label
                       , getInstr :: X86Instruction
                       }

newtype X86LinesPrinter = PrintLines [X86Line]
newtype X86BasicBlocksPrinter = PrintBlocks [[X86Line]]

instance Show X86Line where
  show line@(X86Line label instr) =
    showAsmLine defaultLabelWidth x86InstructionIndent label (Just (show instr))

instance Show X86LinesPrinter where
  show (PrintLines lines) = unlines . map show $ lines

instance Show X86BasicBlocksPrinter where
  show (PrintBlocks blocks) = unlines . map show $ map PrintLines blocks


setLabel :: X86Label -> [X86Instruction] -> [X86Line]
setLabel _ [] = x86InternalError "Can not label an empty set of x86 instructions"
setLabel label (i : is) = X86Line (Just label) i : map (X86Line Nothing) is

fromInstr :: X86Instruction -> X86Line
fromInstr = X86Line Nothing


getOperands :: X86Instruction -> [X86Operand]
getOperands (Xor op1 op2) = [op1, op2]
getOperands (Or op1 op2) = [op1, op2]
getOperands (And op1 op2) = [op1, op2]
getOperands (XAdd op1 op2) = [op1, op2]
getOperands (XSub op1 op2) = [op1, op2]
getOperands (Imul op1) = [op1]
getOperands (Idiv op1) = [op1]
getOperands (Mov op1 op2) = [op1, op2]
getOperands (Cmp op1 op2) = [op1, op2]
getOperands (SetCond _ op1) = [op1]
getOperands (Push op1) = [op1]
getOperands (Pop op1) = [op1]
getOperands _ = []

mapOperands :: (X86Operand -> X86Operand) -> X86Instruction -> X86Instruction
mapOperands f (Xor op1 op2) = Xor (f op1) (f op2)
mapOperands f (Or op1 op2) = Or (f op1) (f op2)
mapOperands f (And op1 op2) = And (f op1) (f op2)
mapOperands f (XAdd op1 op2) = XAdd (f op1) (f op2)
mapOperands f (XSub op1 op2) = XSub (f op1) (f op2)
mapOperands f (Imul op1) = Imul (f op1)
mapOperands f (Idiv op1) = Idiv (f op1)
mapOperands f (Mov op1 op2) = Mov (f op1) (f op2)
mapOperands f (Cmp op1 op2) = Cmp (f op1) (f op2)
mapOperands f (SetCond cond op1) = SetCond cond (f op1)
mapOperands f (Push op1) = Push (f op1)
mapOperands f (Pop op1) = Pop (f op1)
mapOperands _ operandLess = operandLess


malignifyVarName :: VarName -> Symbol
malignifyVarName x = "var_" ++ x


machineInstructionToX86 :: Instruction -> [X86Instruction]
machineInstructionToX86 E = [ Xor (Register Rdi) (Register Rdi)
                            , Call $ Global "exit"
                            ]
machineInstructionToX86 R = [ Call $ Global "runtime_read"
                            , Push $ Register Rax
                            ]
machineInstructionToX86 W = [ Pop $ Register Rdi
                            , Call $ Global "runtime_write"
                            ]
machineInstructionToX86 (I n) = [ Push $ Immediate (fromIntegral n) ]
machineInstructionToX86 (L x) = [ Push $ Symbol (malignifyVarName x) ]
machineInstructionToX86 (S x) = [ Pop $ Symbol (malignifyVarName x) ]
machineInstructionToX86 (B op) = binaryOperatorToX86 op
machineInstructionToX86 (J addr) = [ Jmp $ Local addr ]
machineInstructionToX86 (JT addr) = [ Pop $ Register Rax
                                    , Or (Register Rax) (Register Rax)
                                    , JmpCond IfNz (Local addr)
                                    ]
machineInstructionToX86 (JF addr) = [ Pop $ Register Rax
                                    , Or (Register Rax) (Register Rax)
                                    , JmpCond IfZ (Local addr)
                                    ]


simpleBinOpToX86 :: (X86Operand -> X86Operand -> X86Instruction) -> [X86Instruction]
simpleBinOpToX86 mnemonic = [ Pop $ Register Rcx
                            , mnemonic (Indirect Rsp) (Register Rcx)  -- Intel Order for Operands
                            ]

divModToX86 :: X86Reg -> [X86Instruction]
divModToX86 resultReg = [ Pop $ Register Rcx
                        , Pop $ Register Rax
                        , Cqo
                        , Idiv $ Register Rcx
                        , Push $ Register resultReg
                        ]

comparisonToX86 :: X86Condition -> [X86Instruction]
comparisonToX86 cond = [ Pop $ Register Rcx
                       , Pop $ Register Rax
                       , Cmp (Register Rax) (Register Rcx)  -- Intel Order for Operands
                       , SetCond cond $ Register Rbl
                       , Push $ Register Rbx
                       ]

binaryOperatorToX86 :: BinaryOperator -> [X86Instruction]
binaryOperatorToX86 Mul = [ Pop $ Register Rax
                          , Imul $ Indirect Rsp
                          , Mov (Indirect Rsp) (Register Rax)  -- Intel Order for Operands
                          ]
binaryOperatorToX86 Add = simpleBinOpToX86 XAdd
binaryOperatorToX86 Sub = simpleBinOpToX86 XSub
binaryOperatorToX86 Disj = simpleBinOpToX86 Or
binaryOperatorToX86 Conj = simpleBinOpToX86 And

binaryOperatorToX86 Mod = divModToX86 Rdx
binaryOperatorToX86 Div = divModToX86 Rax

binaryOperatorToX86 Lt = comparisonToX86 IfL
binaryOperatorToX86 Gt = comparisonToX86 IfG
binaryOperatorToX86 Eq = comparisonToX86 IfE
binaryOperatorToX86 Neq = comparisonToX86 IfNe
binaryOperatorToX86 Le = comparisonToX86 IfLe
binaryOperatorToX86 Ge = comparisonToX86 IfGe


machineProgramToX86Lines :: SMProgram -> [X86Line]
machineProgramToX86Lines (SMProgram instrs) =
  setLabel (Global "main") [ Xor (Register Rbx) (Register Rbx) ] :
  zipWith (\instr addr -> setLabel (Local addr) (machineInstructionToX86 instr)) instrs [0..]
  |> concat
  |> optimize


jumpTargets :: [X86Line] -> Set.Set X86Label
jumpTargets = Set.fromList . mapMaybe jumpTarget . map getInstr

isUnconditionalBranch :: X86Instruction -> Bool
isUnconditionalBranch (Jmp _) = True
isUnconditionalBranch (Call (Global "exit")) = True
isUnconditionalBranch _ = False

isConditionalBranch :: X86Instruction -> Bool
isConditionalBranch (JmpCond _ _) = True
isConditionalBranch _ = False

isBranch :: X86Instruction -> Bool
isBranch instr = isConditionalBranch instr || isUnconditionalBranch instr

freeLocalLabelNumber :: [X86Line] -> Addr
freeLocalLabelNumber = foldl step 0
  where step acc (X86Line (Just (Local addr)) _) = max acc (addr + 1)
        step acc _ = acc

ensureLabel :: Addr -> X86Line -> (X86Line, Addr)
ensureLabel freeLabelNumber line@(X86Line (Just _) _) = (line, freeLabelNumber)
ensureLabel freeLabelNumber (X86Line Nothing instr) =
  (X86Line (Just $ Local freeLabelNumber) instr, freeLabelNumber + 1)

ensureBlocksAreLabeled :: [[X86Line]] -> [[X86Line]]
ensureBlocksAreLabeled lines = fst . foldr step ([], freeLocalLabelNumber (concat lines)) $ lines
  where step (line : rest) (acc, freeNumber) = let (labeledLine, newNumber) = ensureLabel freeNumber line
                                               in  ((labeledLine : rest) : acc, newNumber)
        step [] (acc, freeNumber) = ([] : acc, freeNumber)

splitByBasicBlockBoundsUnsafe :: [X86Line] -> [[X86Line]]
splitByBasicBlockBoundsUnsafe lines = fst . foldr step ([[]], (Nothing, Nop)) $ lines
  where step line@(X86Line label instr) (acc@(basicBlock : bbs), (nextLineLabel, nextInstr))
          | isUnconditionalBranch instr
            || isConditionalBranch instr && not (isUnconditionalBranch nextInstr)
            || maybe False (flip Set.member targets) nextLineLabel = ([line] : acc, (label, instr))
          | otherwise = ((line : basicBlock) : bbs, (label, instr))
        targets = jumpTargets lines

makeMovable :: [[X86Line]] -> [[X86Line]]
makeMovable blocks@(_ : rest) = zipWith checkEnd blocks rest
  where checkEnd current@(_ : _) nextBlock =
          if isUnconditionalBranch . getInstr . last $ current then current
          else current ++ case nextBlock of
                            (X86Line (Just nextLabel) _ : _) -> [fromInstr $ Jmp nextLabel]
                            [] -> []
                            _ -> x86InternalError ("makeMovable: list of lists of lines must end with empty list"
                                                ++ " and each list must begin with labeled instruction")
        checkEnd _ _ = x86InternalError "makeMovable: each non-last list of lines must be non-empty"

splitByBasicBlockBounds :: [X86Line] -> [[X86Line]]
splitByBasicBlockBounds = makeMovable . ensureBlocksAreLabeled . splitByBasicBlockBoundsUnsafe


linearize :: [[X86Line]] -> [X86Line]
linearize [] = []
linearize (basicBlock@(_ : _ : _) : tail@(((X86Line (Just label) _) : _) : _))
  | (jumpTarget . getInstr . last) basicBlock == Just label = init basicBlock ++ linearize tail
linearize (basicBlock : tail) = basicBlock ++ linearize tail


shuffleBasicBlocksForTest :: [X86Line] -> [X86Line]
shuffleBasicBlocksForTest lines =
  lines |> backAndForth
        |> backAndForth
        |> reverse' reverse
        |> backAndForth
        |> reverse' swaps
        |> backAndForth
        |> reverse' swaps3
        |> reverse' reverse
        |> backAndForth
        |> reverse' reverse
        |> reverse' swaps
        |> backAndForth
    where backAndForth = linearize . splitByBasicBlockBounds
          reverse' tactic ls | (first : rest) <- splitByBasicBlockBounds ls = linearize (first : tactic rest)
          swaps (b1 : b2 : bbs) = b2 : b1 : swaps bbs
          swaps shorter = shorter
          swaps3 (b1 : b2 : b3 : bbs) = b3 : b1 : b2 : swaps bbs
          swaps3 shorter = shorter

manyJumpsTestCase :: [X86Line]
manyJumpsTestCase =
  let readValue = setLabel (Global "main") $ machineInstructionToX86 R
      lessLabel = Global "less"
      greaterLabel = Global "greater"
      afterSwitchLabel = Global "after_switch"
      switch = map fromInstr [ Cmp (Indirect Rsp) (Immediate 0)
                             , JmpCond IfL lessLabel
                             , JmpCond IfG greaterLabel
                             ]
      ifZeroBB = [ fromInstr $ Jmp afterSwitchLabel ]
      ifLessBB = setLabel lessLabel [ Mov (Indirect Rsp) (Immediate (-1))
                                    , Jmp afterSwitchLabel
                                    ]
      ifGreaterBB = setLabel greaterLabel [ Mov (Indirect Rsp) (Immediate 1) ]
      writeResult = setLabel afterSwitchLabel $ machineInstructionToX86 W
      programEnd = map fromInstr $ machineInstructionToX86 E
  in  readValue ++ switch ++ ifZeroBB ++ ifLessBB ++ ifGreaterBB ++ writeResult ++ programEnd


allocateRegistersOpt :: [X86Line] -> [X86Line]
allocateRegistersOpt lines =
  let replacement = zip (varSymbols lines) [R12, R13, R14, R15]
      toRegister (Symbol symbol) | Just reg <- lookup symbol replacement = Register reg
      toRegister other = other
  in  map (\(X86Line label instr) -> X86Line label (mapOperands toRegister instr)) lines

doSomeGlobalOptimizations :: [[X86Line] -> [X86Line]] -> [X86Line] -> [X86Line]
doSomeGlobalOptimizations optimizations = foldl (.) id optimizations

doGlobalOptimizations :: [X86Line] -> [X86Line]
doGlobalOptimizations = doSomeGlobalOptimizations
  [ allocateRegistersOpt
  ]


pushPopToMovOpt :: [X86Line] -> [X86Line]
pushPopToMovOpt [] = []
pushPopToMovOpt (line1@(X86Line _ (Push (Symbol _))) : line2@(X86Line _ (Pop (Symbol _))) : rest) =
  line1 : line2 : pushPopToMovOpt rest
pushPopToMovOpt (X86Line l1 (Push src) : X86Line l2 (Pop dst) : rest) =
  X86Line (l1 `mplus` l2) (Mov dst src) : pushPopToMovOpt rest
pushPopToMovOpt (line : rest) = line : pushPopToMovOpt rest

movPopToMovOpt :: [X86Line] -> [X86Line]
movPopToMovOpt [] = []
movPopToMovOpt ((X86Line l1 (Mov (Indirect Rsp) src)) : (X86Line l2 (Pop dst)) : rest) =
  X86Line l1 (Mov dst src) : X86Line l2 (XAdd (Register Rsp) (Immediate 8)) : movPopToMovOpt rest
movPopToMovOpt (line : rest) = line : movPopToMovOpt rest

setCondMovJumpToJumpCond :: [X86Line] -> [X86Line]
setCondMovJumpToJumpCond [] = []
setCondMovJumpToJumpCond lines
  | SetCond cond (Register Rbl)
  : Mov (Register Rax) (Register Rbx)
  : Or (Register Rax) (Register Rax)
  : JmpCond jmpCond label
  : _ <- map getInstr lines = X86Line (foldr1 mplus $ map getLabel $ take 4 lines)
                                      (JmpCond (combineConds jmpCond cond) label)
                            : drop 4 lines
    where combineConds IfZ IfE = IfNe
          combineConds IfZ IfNe = IfE
          combineConds IfZ IfZ = IfNz
          combineConds IfZ IfNz = IfZ
          combineConds IfZ IfL = IfGe
          combineConds IfZ IfG = IfLe
          combineConds IfZ IfLe = IfG
          combineConds IfZ IfGe = IfL
          combineConds IfNz someCond = someCond
          combineConds _ _ = x86InternalError "setCondMovJumpToJumpCond: unsupported JmpCond condition"
setCondMovJumpToJumpCond (line : rest) = line : setCondMovJumpToJumpCond rest

doSomePerBasicBlockOptimizations :: [[X86Line] -> [X86Line]] -> [X86Line] -> [X86Line]
doSomePerBasicBlockOptimizations optimizations =
  linearize . map (foldl (.) id optimizations) . splitByBasicBlockBounds

doPerBasicBlockOptimizations :: [X86Line] -> [X86Line]
doPerBasicBlockOptimizations = doSomePerBasicBlockOptimizations
  [ setCondMovJumpToJumpCond
  , movPopToMovOpt
  , pushPopToMovOpt
  ]


movZeroToXorOpt :: X86Instruction -> X86Instruction
movZeroToXorOpt (Mov reg@(Register _) (Immediate 0)) = Xor reg reg
movZeroToXorOpt instr = instr

doSomePerInstructionOptimizations :: [X86Instruction -> X86Instruction] -> [X86Line] -> [X86Line]
doSomePerInstructionOptimizations optimizations = map (\(X86Line label instr) -> X86Line label (opt instr))
  where opt = foldl (.) id optimizations

doPerInstructionOptimizations :: [X86Line] -> [X86Line]
doPerInstructionOptimizations = doSomePerInstructionOptimizations
  [ movZeroToXorOpt
  ]

doOptimizations :: [[X86Line] -> [X86Line]] -> [X86Line] -> [X86Line]
doOptimizations optimizations = foldl (.) id optimizations

optimize :: [X86Line] -> [X86Line]
optimize = doOptimizations
  [ doPerInstructionOptimizations
  , doPerBasicBlockOptimizations
  , doGlobalOptimizations
  ]



type Size = Int
type Level = Int  -- for pretty-printing purposes only

intSize :: Int
intSize = 8

data GasDirective = Globl Symbol
                  | Comm Symbol Size

data GasInstruction = GasInstruction X86Instruction
                    | GasDirective GasDirective

newtype GasLine = GasLine (Level, Maybe X86Label, Maybe GasInstruction)
newtype GasLinesPrinter = PrintGasLines [GasLine]

instance Show GasLine where
  show (GasLine (level, label, instr)) =
    showAsmLine defaultLabelWidth (x86InstructionIndent * level) label (instr >>= (return . show))

instance Show GasLinesPrinter where
  show (PrintGasLines lines) = unlines . map show $ lines


fromGasLine :: GasLine -> Maybe X86Line
fromGasLine (GasLine (_, label, Just (GasInstruction instr))) = Just $ X86Line label instr
fromGasLine _ = Nothing

appendEmptyLine :: [GasLine] -> [GasLine]
appendEmptyLine [] = []
appendEmptyLine lines@(GasLine (level, _, _) : _) = lines ++ [GasLine (level, Nothing, Nothing)]

varSymbols :: [X86Line] -> [Symbol]
varSymbols = nub . mapMaybe getSymbol . concatMap (getOperands . getInstr)
  where getSymbol (Symbol symbol) = Just symbol
        getSymbol _ = Nothing

allocateSpaceForVars :: [X86Line] -> [GasLine]
allocateSpaceForVars x86Lines =
  x86Lines |> varSymbols
           |> map (\varName -> GasLine (0, Nothing, Just $ GasDirective $ Comm varName intSize))
           |> appendEmptyLine

globalSymbols :: [X86Line] -> [Symbol]
globalSymbols = nub . mapMaybe extractSymbol
  where extractSymbol (X86Line (Just (Global symbol)) _) = Just symbol
        extractSymbol _ = Nothing

declareGlobalSymbols :: [X86Line] -> [GasLine]
declareGlobalSymbols x86Lines =
 x86Lines |> globalSymbols
          |> map (\symbol -> GasLine (0, Nothing, Just $ GasDirective $ Globl symbol))
          |> appendEmptyLine


renderGasLines :: [X86Line] -> [GasLine]
renderGasLines x86Lines =
  declareGlobalSymbols x86Lines ++
  allocateSpaceForVars x86Lines ++
  ( x86Lines
     |> map (\(X86Line label instr) -> GasLine(1, label, Just $ GasInstruction instr))
  )


mnemonicWidth :: Int
mnemonicWidth = 5

defaultLabelWidth :: Int
defaultLabelWidth = 6

localLabelWidth :: [X86Line] -> Int
localLabelWidth lines = let maxLabel = max 0 $ freeLocalLabelNumber lines - 1
                            len = length (show $ Local maxLabel) + 1
                        in  len + len `mod` 2

x86InstructionIndent :: Int
x86InstructionIndent = 8

withSOperands :: String -> [String] -> String
withSOperands mnemonic operands = ljust mnemonicWidth mnemonic ++ " " ++ intercalate ", " operands

withOperands :: (Show a) => String -> [a] -> String
withOperands mnemonic operands = withSOperands mnemonic (map show operands)

instance Show GasDirective where
  show (Globl symbol) = withSOperands ".globl" [symbol]
  show (Comm symbol size) = withSOperands ".comm" [symbol, show size]

instance Show GasInstruction where
  show (GasInstruction instr) = show instr
  show (GasDirective directive) = show directive

instance Show X86Reg where
  show Rax = "%rax"
  show Rcx = "%rcx"
  show Rbx = "%rbx"
  show Rdx = "%rdx"
  show Rdi = "%rdi"
  show Rsp = "%rsp"
  show Rbl = "%bl"
  show R12 = "%r12"
  show R13 = "%r13"
  show R14 = "%r14"
  show R15 = "%r15"

instance Show X86Operand where
  show (Register reg) = show reg
  show (Symbol symbol) = symbol
  show (Immediate n) = "$" ++ show n
  show (Indirect reg) = "(" ++ show reg ++ ")"

instance Show X86Label where
  show (Local addr) = ".L" ++ show addr
  show (Global symbol) = symbol

instance Show X86Condition where
  show IfE = "e"
  show IfNe = "ne"
  show IfZ = "z"
  show IfNz = "nz"
  show IfL = "l"
  show IfG = "g"
  show IfLe = "le"
  show IfGe = "ge"

instance Show X86Instruction where
  show (Xor dst src) = withOperands "xorq" [src, dst]
  show (Or dst src) = withOperands "orq" [src, dst]
  show (And dst src) = withOperands "andq" [src, dst]
  show (XAdd dst src) = withOperands "addq" [src, dst]
  show (Imul src) = withOperands "imulq" [src]
  show (XSub dst src) = withOperands "subq" [src, dst]
  show Cqo = "cqto"
  show (Idiv operand) = withOperands "idivq" [operand]
  show (Mov dst src) = withOperands "movq" [src, dst]
  show (Cmp src1 src2) = withOperands "cmpq" [src2, src1]
  show (SetCond cond dst) = withOperands ("set" ++ show cond) [dst]
  show (JmpCond cond label) = withOperands ("j" ++ show cond) [label]
  show (Jmp label) = withOperands "jmp" [label]
  show (Call src) = withOperands "call" [src]
  show (Push src) = withOperands "pushq" [src]
  show (Pop dst) = withOperands "popq" [dst]
  show Nop = "nop"

showAsmLine :: Int -> Int -> Maybe X86Label -> Maybe String -> String
showAsmLine defaultLabelWidth instrIndent label instr =
  let label' = maybe "" (rjust defaultLabelWidth . (++ ":") . show) label
  in  if length' label' <= instrIndent
      then maybe label' (ljust instrIndent label' ++) instr
      else label' ++ maybe "" (("\n" ++ replicate instrIndent ' ') ++) instr
        where length' s = if length s == 0 then 0 else length s + 1


newtype GasSource = GasSource [GasLine]

instance Show GasSource where
  show (GasSource lines) = concat $ map ((++ "\n"). showGasLine) lines
    where showGasLine (GasLine (level, label, instr)) =
            showAsmLine labelWidth (x86InstructionIndent * level) label (instr >>= (return . show))
          labelWidth = localLabelWidth $ mapMaybe fromGasLine lines


renderGasSource :: SMProgram -> GasSource
renderGasSource = GasSource . renderGasLines . machineProgramToX86Lines

gasStringOfProgram :: Statement -> String
gasStringOfProgram = show . renderGasSource . compileProgram

compileAndWriteGasSourceFile :: FilePath -> Statement -> IO ()
compileAndWriteGasSourceFile filename = writeFile filename . gasStringOfProgram

compileAndWriteBinaryExecutable :: FilePath -> Statement -> IO Bool
compileAndWriteBinaryExecutable exeFileName program = do
  let sourceFilename = exeFileName ++ ".s"
  compileAndWriteGasSourceFile sourceFilename program
  gccExecutable <- findExecutable gccCompatibleCompiler
  case gccExecutable of
    Just gccPath -> do
      gccExitCode <- rawSystem gccPath ["runtime.c", sourceFilename, "-o", exeFileName]
      exeOk <- doesFileExist exeFileName
      return $ assert (gccExitCode == ExitSuccess) exeOk
    Nothing -> do
      hPutStrLn stderr (gccCompatibleCompiler ++ " not found")
      return False


checkBinaryProgram :: FilePath -> Statement -> Stream -> Stream -> IO Bool
checkBinaryProgram exeFileName program input expected = do
  exeOk <- compileAndWriteBinaryExecutable exeFileName program
  if not exeOk then return False
  else do actualString <- readProcess ("./" ++ exeFileName) [] (unlines $ map show input)
          let verdict = lines actualString == map show expected
          return $ assert verdict verdict

prettyCheckOfBinaryProgram :: FilePath -> Statement -> Stream -> Stream -> IO ()
prettyCheckOfBinaryProgram exeFileName program input expected = do
  ok <- checkBinaryProgram exeFileName program input expected
  let verdict = if ok then "OK" else "FAIL"
  putStrLn $ "Compile to x86-64 machine code and test binary program " ++ exeFileName ++ ": " ++ verdict



program7BigBinaryCheck :: IO ()
program7BigBinaryCheck = prettyCheckOfBinaryProgram "program7" testProgram7 (len : testList) (len : reverse testList)
  where testList = [0, 0, 0, 6, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 1] ++ replicate 1008 0
        len = fromIntegral $ length testList


main :: IO ()
main = do
  putStrLn test1Checked
  putStrLn test2Checked
  putStrLn ""
  putStrLn checkedProgram1
  putStrLn checkedHistory1
  putStrLn ""
  putStrLn checkedHistory2
  putStrLn ""
  putStrLn checkedHistory3
  putStrLn ""
  putStrLn test1Parsing
  putStrLn test2Parsing
  putStrLn ""
  putStrLn testMachineChecked
  putStrLn testMachineExpressionValue1
  putStrLn testMachineExpressionValue2
  putStrLn ""
  putStrLn checkedCompiledProgram1
  putStrLn ("Compiler Output:\n" ++ show (compileProgram testProgram1))
  putStrLn "\n"
  putStrLn checkedCompiledProgram2
  putStrLn ("Compiler Output:\n" ++ show (compileProgram testProgram2))
  putStrLn "\n"
  putStrLn checkedCompiledProgram3
  putStrLn ("Compiler Output:\n" ++ show (compileProgram testProgram3))
  putStrLn "\n"
  putStrLn checkedProgram7
  putStrLn "\n"
  prettyCheckOfBinaryProgram "program1" testProgram1 [8] [40320]
  prettyCheckOfBinaryProgram "program2" testProgram2 [832040, 1346269] [1]
  prettyCheckOfBinaryProgram "program3" testProgram3 [12] [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]
  prettyCheckOfBinaryProgram "program4" (programOfExpression test1Env test1Expr) [] [test1Expected]
  prettyCheckOfBinaryProgram "program5" (programOfExpression test2Env test2Expr) [] [test2Expected]
  putStrLn ""
  prettyCheckOfBinaryProgram "program6" testProgram6 [2] [0, 0, 0, 1, 1, 1, 1, 0]
  prettyCheckOfBinaryProgram "program6" testProgram6 [3] [0, 0, 0, 1, 0, 2, 1, 2, 2, 2, 2, 1, 2, 0, 1, 0, 1, 1]
  putStrLn ""
  prettyCheckOfBinaryProgram "program7" testProgram7 [0] [0]
  prettyCheckOfBinaryProgram "program7" testProgram7 [3, 1, 2, 3] [3, 3, 2, 1]
  prettyCheckOfBinaryProgram "program7" testProgram7 [9, 7, 1, 0, 2, 3, 5, 1, 2, 0] [9, 0, 2, 1, 5, 3, 2, 0, 1, 7]
  program7BigBinaryCheck
