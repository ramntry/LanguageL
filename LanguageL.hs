module Main where

import Control.Exception.Base (assert)
import Data.Function (on)
import Data.List (intercalate)
import qualified Data.Map as Map

type ErrorHandler a = String -> a

languageLError message = error ("[Language L] " ++ message ++ ".")
internalError message = languageLError ("Internal Error: " ++ message)
expressionError message = languageLError ("Expression Evaluation: " ++ message)
programError message = languageLError ("Program Execution: " ++ message)

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


semaForBinOp :: (Integer -> Integer -> Integer) -> Expression -> Expression -> Semantics
semaForBinOp op e1 e2 = \s -> let (a1, s1) = sema e1 s
                                  (a2, s2) = sema e2 s1
                              in  (a1 `op` a2, s2)

semaForBoolOp :: (Integer -> Integer -> Bool) -> Expression -> Expression -> Semantics
semaForBoolOp op = semaForBinOp (\n m -> fromBool (n `op` m))

sema :: Expression -> Semantics
sema (C n) = \s -> (n, s)
sema (V x) = \s -> (s.$ x, s)

sema (Inc x) = \s -> (s.$ x, s <-- x .= s.$ x + 1)
sema (Dec x) = \s -> (s.$ x, s <-- x .= s.$ x - 1)

sema (e1 :+ e2) = semaForBinOp (+) e1 e2
sema (e1 :* e2) = semaForBinOp (*) e1 e2
sema (e1 :- e2) = semaForBinOp (-) e1 e2
sema (e1 :/ e2) = semaForBinOp (\n m -> n `div` divisor m) e1 e2
sema (e1 :% e2) = semaForBinOp (\n m -> n `mod` divisor m) e1 e2

sema (e1 :< e2) = semaForBoolOp (<) e1 e2
sema (e1 :> e2) = semaForBoolOp (>) e1 e2
sema (e1 :== e2) = semaForBoolOp (==) e1 e2
sema (e1 :!= e2) = semaForBoolOp (/=) e1 e2
sema (e1 :<= e2) = semaForBoolOp (<=) e1 e2
sema (e1 :>= e2) = semaForBoolOp (>=) e1 e2

sema (e1 :|| e2) = semaForBoolOp ((||) `on` bool expressionError) e1 e2
sema (e1 :&& e2) = semaForBoolOp ((&&) `on` bool expressionError) e1 e2


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

bigStep _ _ = programError "Can not read from an empty input stream"


initialConf :: Stream -> Configuration
initialConf input = (emptyState, input, [])

programSema :: Statement -> Stream -> Stream
programSema statement input = case bigStep statement (initialConf input) of
                                (s, [], output) -> forseState s $ reverse output
                                _ -> programError "Program has completed with non-empty input stream"
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


checkProgram :: Statement -> Stream -> Stream -> String
checkProgram program input expected = assert (actual == expected) $
  "The program below has completed execution on an input stream " ++ showStream input ++
  " with output stream " ++ showStream actual ++
  " while expected output is " ++ showStream expected ++ ".\n" ++
  showProgram program ++ "\n"
    where actual = programSema program input
          showStream = intercalate " " . map show

checkHistory :: Statement -> Stream -> Configuration -> String
checkHistory program input expected = assert (actual == expected) $
  "Execution history: (expected configuration is " ++ show expected ++ ")" ++
  "\n\n" ++ show history ++ "\n"
    where history = stepByStep program input
          actual = configurationOfHistory history

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

testProgram3 =
  Read "n":.
  "curr" ::= C 1:.
  "next" ::= C 1:.
  While (Dec "n" :!= C 0) (
    Write (V "curr"):.
    "tmp" ::= V "next":.
    "next" ::= V "curr" :+ V "next":.
    "curr" ::= V "tmp")

checkedProgram1 :: String
checkedProgram1 = checkProgram testProgram1 [6] [720]

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
