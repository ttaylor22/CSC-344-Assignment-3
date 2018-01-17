module Lib where

import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec

data ExprTree = Const { rule :: [Char] }
              | EmptyExpr { epty :: [Char] }
              | Number { int :: Int }
              | Expr  { rule :: [Char], 
                        arg1 :: ExprTree, 
                        arg2 :: ExprTree }
              | CondIntroRuleExpr { rule :: [Char],
                                    arg1 :: ExprTree }
              | CondElimRuleExpr { rule :: [Char],
                                   arg1 :: ExprTree,
                                   num1 :: ExprTree,
                                   num2 :: ExprTree }
              | ConjIntroRuleExpr { rule :: [Char],
                                    arg1 :: ExprTree,
                                    num1 :: ExprTree,
                                    num2 :: ExprTree }
              | ConjElimRuleExpr { rule :: [Char],
                                   arg1 :: ExprTree,
                                   num1 :: ExprTree }
              | Hypothesis { num1 :: ExprTree,
                             rule :: [Char],
                             arg1 :: ExprTree }
              | Derivation { num1 :: ExprTree,
                             arg1 :: ExprTree }
              | Subproof { arg1 :: ExprTree,
                           str :: [Char],
                           arg2 :: ExprTree,
                           arg3 :: [ExprTree] }
              | NonDischarge { str :: [Char], 
                              arg1 :: ExprTree }
              | Proof { num1 :: ExprTree, 
                        arg1 :: ExprTree } deriving (Show)

constexpr :: GenParser Char st ExprTree
constexpr = do 
    exp <- (many (noneOf "() "))
    return (Const exp)

numberexpr :: GenParser Char st ExprTree
numberexpr = do 
    exp <- (many (digit))
    return (Number (readint exp))

readint :: String -> Int
readint = read

ifexpr :: GenParser Char st ExprTree
ifexpr = do
    char '('
    string "if"
    char ' '
    ant <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ' '
    cq <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ')'
    return (Expr "if" ant cq)

andexpr :: GenParser Char st ExprTree
andexpr = do 
    char '('
    string "and"
    char ' '
    ant <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ' '
    cq <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ')'
    return (Expr "and" ant cq)

proof :: GenParser Char st ExprTree
proof = do
    num <- numberexpr
    char ' '
    ant <- subproof
    return (Proof num ant)

subproof :: GenParser Char st ExprTree
subproof = do
    char '('
    rule <- condIntroRule
    char '\n'
    char '('
    string "proof"
    hyp <- hypothesis
    cw <- many1 derivationLine
    char ')'
    char ')'
    return (Subproof rule "proof" hyp cw)

hypothesis :: GenParser Char st ExprTree
hypothesis = do
    char '\n'
    num1 <- numberexpr
    char ' '
    char '('
    string "hyp"
    char ' '
    ant <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ')'
    return (Hypothesis num1 "hyp" ant)

derivationLine :: GenParser Char st ExprTree
derivationLine = do
    char '\n'
    num1 <- numberexpr
    char ' '
    ant <- try(subproof) <|> try(nonDischargeRule)
    return (Derivation num1 ant)

nonDischargeRule :: GenParser Char st ExprTree
nonDischargeRule = do
    char '('
    ant <- try(condElimRule) <|> try(conjElimRule) <|> try(conjIntroRule)
    char ')'
    return (NonDischarge "nondischarge" ant)

condIntroRule :: GenParser Char st ExprTree
condIntroRule = do
    string "->I"
    char ' '
    ant <- ifexpr
    return (CondIntroRuleExpr "->I" ant)

condElimRule :: GenParser Char st ExprTree
condElimRule = do 
    string "->E"
    char ' '
    ant <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ' '
    num1 <- numberexpr
    char ' '
    num2 <- numberexpr
    return (CondElimRuleExpr "->E" ant num1 num2)

conjIntroRule :: GenParser Char st ExprTree
conjIntroRule = do
    string "&I"
    char ' '
    ant <- andexpr
    char ' '
    num1 <- numberexpr
    char ' '
    num2 <- numberexpr
    return (ConjIntroRuleExpr "&I" ant num1 num2)

conjElimRule :: GenParser Char st ExprTree
conjElimRule = do
    string "&E"
    char ' '
    ant <- try(ifexpr) <|> try(andexpr) <|> constexpr
    char ' '
    num1 <- numberexpr
    return (ConjElimRuleExpr "&E" ant num1)

listProof :: ExprTree -> [ExprTree]
listProof = do
    subprf <- arg1
    let dischrg = arg1 subprf
    let hypoth = arg1 (arg2 subprf)
    let derivs = arg3 subprf
    let l = [dischrg,hypoth]
    let ll = map listDeriv derivs
    let lll = concat ll
    let out = l ++ lll
    return out

listSubproof :: ExprTree -> [ExprTree]
listSubproof = do
    dischrg <- arg1 
    prehypoth <- arg2
    derivs <- arg3
    let hypoth = arg1 prehypoth
    let l = [dischrg,hypoth]
    let ll = map listDeriv derivs
    let lll = concat ll
    let out = l ++ lll
    return out

listDeriv :: ExprTree -> [ExprTree]
listDeriv = do
    deriv <- arg1
    let l = if (str deriv) == "nondischarge" 
            then listNonDischarge deriv
            else listSubproof deriv
    return l

listNonDischarge :: ExprTree -> [ExprTree]
listNonDischarge = do
    out <- arg1
    return [out]

eval :: [ExprTree] ->  Bool
eval a = do
    let n = Number 0
    let toeval = [n] ++ a
    let c = subeval toeval
    c

subeval :: [ExprTree] -> Bool
subeval list = do
    let itmp = int (list !! 0)
    let i = itmp + 1
    let current = list !! i
    let d = if (rule current == "if")
            then do
                let prev = list !! (i-1)
                let l = [current, (arg1 (arg1 prev))]
                let b = compareExpr l
                b
            else if (rule current == "and")
                then do
                    let prev = list !! (i-1)
                    let l = [current, (arg1 (arg1 prev))]
                    let b = compareExpr l
                    b
                else if (rule current == "->I" && i /= 0)
                    then do
                        let ii = findLastDischarge list
                        let iiexpr = Number ii
                        let prev = list !! ii
                        let tmp = tail list
                        let listin = [iiexpr] ++ tmp
                        let b1 = checkDischarge current
                        let b2 = compareDischarge (listin ++ [current, prev])
                        let b = (b1)
                        b
                    else if (rule current == "->E") 
                        then do 
                            let tmp = arg1 current
                            if i == int (num1 current)
                            then False
                            else do
                                let tmp1 = list !! int (num1 current)
                                let tmp2 = list !! int (num2 current)
                                let tmp3 = [tmp,tmp1,tmp2]
                                let b = condElimEval tmp3
                                b
                        else if (rule current == "&I")
                            then do
                                let tmp = arg1 current
                                if i == int (num1 current)
                                then False
                                else do
                                    let tmp1 = list !! int (num1 current)
                                    let tmp2 = list !! int (num2 current)
                                    let tmp3 = [tmp,tmp1,tmp2]
                                    let b = conjIntroEval tmp3
                                    b
                            else if (rule current == "&E")
                                then do 
                                    let tmp = arg1 current
                                    let tmp1 = list !! int (num1 current)
                                    if i == int (num1 current)
                                    then False
                                    else do
                                        let tmp2 = [tmp,tmp1]
                                        let b = conjElimEval tmp2
                                        b
                                else if (rule current == "->I")
                                    then checkDischarge (list !! 1)
                                    else do
                                        let prev = list !! (i-1)
                                        let l = [current, (arg1 (arg1 prev))]
                                        let b = compareExpr l
                                        b
    let s = length list
    let n = Number i
    let listnew = [n] ++ (tail list)
    let c = if (i < (s-1))
            then subeval listnew
            else True
    let out = if (c == False || d ==  False)
              then False
              else True
    out

checkDischarge :: ExprTree -> Bool
checkDischarge = do
    arg <- arg1
    let op = rule arg
    let out = (op == "if")
    return out

compareExpr :: [ExprTree] -> Bool
compareExpr = do
    current <- (!! 0)
    prev <- (!! 1)
    let r1 = rule current
    let r2 = rule prev
    let out = if r1 /= r2 
              then False
              else if r1 == "and" || r1 == "if"
                    then do 
                        let l1 = compareExpr [arg1 current, arg1 prev]
                        let l2 = compareExpr [arg2 current, arg2 prev]
                        let lbool = (l1 && l2)
                        lbool
                    else True
    return out

compareDischarge :: [ExprTree] -> Bool
compareDischarge = do
    s <- length 
    current <- (!! (s-2))
    prev <- (!! (s-1))
    list <- take (s-3)
    let i = int (head list)
    let prev2 = arg1 prev
    let a = if (rule prev2 == "if")
              then compareExpr [current, prev2]
              else if (rule prev2 == "and")
                  then do
                  let b1 = compareExpr [current, arg1 prev2]
                  let b2 = compareExpr [current, arg2 prev2]
                  let b = (b1 || b2)
                  b
                  else compareExpr [current, prev2]
    let out = if a == False
              then do
                  if (i /= 0)
                  then do
                      let ii = findLastDischarge list
                      let prev = list !! ii
                      let tmp = tail list
                      let iinc = Number ii
                      let listin = [iinc] ++ tmp
                      let b = compareDischarge (listin ++ [current, prev])
                      b
                  else False
              else True
    return out

isRight (Right _) = True
isRight _        = False

findLastDischarge :: [ExprTree] -> Int
findLastDischarge = do
    f <- (!! 0)
    let n = int f
    let inc = n-1
    a <- (!! inc)
    list <- tail
    let out = if rule a == "->I"
              then inc
              else do 
                  let iinc = Number inc
                  findLastDischarge ([iinc] ++ list)
    return out

condElimEval :: [ExprTree] -> Bool
condElimEval = do
    q <- (!! 0)
    ptmp <- (!! 2)
    pqtmp <- (!! 1)
    let pq = if (rule pqtmp == "->E" || rule pqtmp == "&E" || rule pqtmp == "&I" )
             then arg1 pqtmp
             else pqtmp
    let ptmp1 = if (rule ptmp == "->E" || rule ptmp == "&E" || rule ptmp == "&I" )
                then arg1 ptmp
                else ptmp
    let qfo = if (rule pq == "and" || rule pq == "if")
              then arg2 pq
              else arg2 (arg1 pq)
    let pfo = if (rule pq == "and" || rule pq == "if")
              then arg1 pq
              else arg1 (arg1 pq)
    let p = if (rule ptmp1 == "and" || rule ptmp1 == "if")
            then arg2 ptmp1
            else ptmp1
    let l1 = [q, qfo]
    let l2 = [p, pfo]
    let b1 = compareExpr l1
    let b2 = compareExpr l2
    let out = if (b1 == False || b2 == False)
              then False
              else True
    return out

conjIntroEval :: [ExprTree] -> Bool
conjIntroEval = do
    qtmp <- (!! 2)
    ptmp <- (!! 1)
    let ptmp1 = if (rule ptmp == "->E" || rule ptmp == "&E" || rule ptmp == "&I" || rule ptmp == "->I")
                then arg1 ptmp
                else ptmp
    let qtmp1 = if (rule qtmp == "->E" || rule qtmp == "&E" || rule qtmp == "&I" || rule ptmp == "->I")
                then arg1 qtmp
                else qtmp
    pq <- (!! 0)
    let p = arg1 pq
    let q = arg2 pq
    let l1 = [q, qtmp1]
    let l2 = [p, ptmp1]
    let b1 = compareExpr l1
    let b2 = compareExpr l2
    let out = (b1 && b2)
    return out

conjElimEval :: [ExprTree] -> Bool
conjElimEval = do
    p <- (!! 0)
    pq <- (!! 1)
    let pqtmp = if (rule pq == "->E" || rule pq == "&E" || rule pq == "&I" || rule pq == "->I")
                then arg1 pq
                else pq
    let qfo = if (rule pqtmp == "and" || rule pqtmp == "if")
              then arg2 pqtmp
              else pqtmp
    let pfo = if (rule pqtmp == "and" || rule pqtmp == "if")
              then arg1 pqtmp
              else pqtmp
    let l1 = [p, qfo]
    let l2 = [p, pfo]
    let b1 = compareExpr l1
    let b2 = compareExpr l2
    let out = if (b1 == True || b2 == True)
              then True
              else False
    return out

test :: IO ()
test = do
    contents <- readFile "C:\\Users\\Benjamin\\assignment3\\app\\proof2.txt"
    let parsed = parse proof "" contents
    let out = if (isRight parsed)
              then do
                  let (Right rightparsed) = parsed
                  let l = listProof rightparsed
                  let validation = eval l
                  let out1 = if validation == True
                             then "Valid"
                             else "Invalid"
                  out1
               else do
                   let out = "Invalid"
                   out
    print out

main2 :: IO ()
main2 = do
    contents <- readFile "C:\\Users\\Benjamin\\assignment3\\app\\proof2.txt"
    let parsed = parse proof "" contents
    let (Right rightparsed) = parsed
    let l = listProof rightparsed
    print l
