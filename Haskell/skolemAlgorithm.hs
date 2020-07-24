import Data.List

-- example input: hornFormula = [("(a&b)|(c&d)", "a&b"), ("a", "c")]
-- example input: hornFormula = [("a","b"), ("b","c"), ("a","c")]
-- example input: hornFormula = [("a","a&a"), ("a","a&a"), ("a","a&a")]
-- example input: hornFormula = [("x&y", "x"), ("x|(y&z)","(x|y)&z")]
-- example input: hornFormula = [("x&y", "y"), ("x&y", "x")]
-- example input: s1 = "(((u&v)|(u&w))&(u&x))|((u&v)|((u&w)&(u&x)))"
--                t1 = "(u&v)|((u&w)&(u&x))"
--         Equality 1:
--                s = "(u&v)&((u&w)|(u&x))"
--                t = "u&v"
--         Equality 2:
--                s = "(u&w)&((u&v)|(u&x))"
--                t = "u&w"
--         Equality 3:
--                s = "(u&x)&((u&v)|(u&w))"
--                t = "u&x"
--         Equality 4:
--                s = "((u&w)&(u&x))|(u&v)"
--                t = "u&v"
--         Equality 5:
--                s = "((u&v)&(u&x))|(u&w)"
--                t = "u&w"
--         Equality 6:
--                s = "((u&v)&(u&w))|(u&x)"
--                t = "u&x"


-- returns [(1,4),(0,5)] for ((ab))
parenPairs :: String -> [(Int, Int)]
parenPairs = go 0 []
  where
    go _ _        []         = []
    go j acc      ('(' : cs) =          go (j + 1) (j : acc) cs
    go j []       (')' : cs) =          go (j + 1) []        cs -- unbalanced parentheses!
    go j (i : is) (')' : cs) = (i, j) : go (j + 1) is        cs
    go j acc      (c   : cs) =          go (j + 1) acc       cs

-- returns index of parenthesis corresponding to first parenthesis
endOfFirstParenPair :: String -> Int
endOfFirstParenPair str = snd ((filter isFirstParenPair (parenPairs str))!!0)

-- checks whether the first entry of a pair of integers is zero
isFirstParenPair :: (Int, Int) -> Bool
isFirstParenPair (a,_) = a == 0

-- strips away brackets: returns 'a&b' for '(a&b)'
stripBracket :: String -> String
stripBracket str
    | str!!0 /= '('                               = str
    | endOfFirstParenPair str == (length str) - 1 = take (length str - 2) (tail str)
    | otherwise                                   = str

-- Can only be applied to conjuctions and disjunctions. returns "a" for "a&b"
first :: String -> String
first str
    | str!!0 /= '(' = [str!!0]
    | otherwise     = stripBracket $ take (endOfFirstParenPair str + 1) str
-- same. returns "b" for "a&b"
second :: String -> String
second str 
    | str!!(length str - 1) /= ')' = [str!!(length str - 1)]
    | str!!0 /= '('                = stripBracket $ reverse
                                                  $ take (length str - 2) (reverse str)
    | otherwise                    = stripBracket $ reverse 
                                                  $ take (length str - endOfFirstParenPair str - 2) 
                                                    (reverse str)


--- step 0
-- generates set of subterms of a single term
subterms :: String -> [String]
subterms "" = []
subterms str 
    | str!!0 /= '(' = nub $ [str] ++ [[str!!0]] 
                          ++ subterms (reverse $ take ((length str) - 2) $ reverse str)
    | otherwise     = nub $ [stripBracket str] 
                          ++ subterms (take (n-1) $ tail str) 
                          ++ subterms (reverse $ take ((length str) - n - 2) $ reverse str)
    where n = endOfFirstParenPair str

-- this is gonna be U
setOfSubterms :: [(String, String)] -> [String]
setOfSubterms hornFormula = nub $ concat listOfIndividualSubterms
    where listOfIndividualSubterms = [subterms a | (a, b) <- hornFormula] 
                                  ++ [subterms b | (a, b) <- hornFormula]



--- Step (a)	

-- input: hornFormula = [(s1, t1), ..., (sk, tk), (s, t)]
-- this is the initial lessThan described in (a)
initialLessThan :: [(String, String)] -> [(String, String)]
initialLessThan list = nub $ (init list) ++ [(b,a) | (a,b) <- (init list)]


--- Step (b)
-- input: U (i.e., setOfSubterms hornFormula)

-- defines what a disjunction is
isDisjunction :: String -> Bool
isDisjunction str
    | length str <= 1              = False
    | str!!0 /= '('                = str!!1 == '|'
    | str!!(length str - 1) == ')' = str!!((endOfFirstParenPair str) + 1) == '|'
    | otherwise                    = str!!(length str - 2) == '|'

-- the initialization of Join in (b)
initialJoin :: [String] -> [(String, String, String)]
initialJoin terms = [(first r, second r, r) | r <- terms, isDisjunction r]


--- Step (c)
-- input: U

-- defines what a conjunction is
isConjunction :: String -> Bool
isConjunction str
    | length str <= 1              = False
    | str!!0 /= '('                = str!!1 == '&'
    | str!!(length str - 1) == ')' = str!!((endOfFirstParenPair str) + 1) == '&'
    | otherwise                    = str!!(length str - 2) == '&'

-- the initialization of Meet in (c)
initialMeet :: [String] -> [(String, String, String)]
initialMeet terms = [(first r, second r, r) | r <- terms, isConjunction r]


--- Step (d)
-- (i) defines the reflexive closure. Only needs to be called once (in the initial thing)
reflexiveClosure :: [String] -> [(String, String)]
reflexiveClosure terms = [(a,a) | a <- terms]

-- (ii) defines the transitive closure
transitiveClosure :: Eq a => [(a,a)] -> [(a,a)]
transitiveClosure xs
    | xs == tmpClosure = xs
    | otherwise        = transitiveClosure tmpClosure
    where tmpClosure = nub $ xs ++ [(a,c) | (a,b) <- xs, (b',c) <- xs, b == b']

-- (iii) if (x,y,z) in Meet, add (z,x) and (z,y) to <=
-- returns what should be added to <=
ruleThree :: [(String, String, String)] -> [(String, String)]
ruleThree meet = nub $ [(z,x) | (x,y,z) <- meet] ++ [(z,y) | (x,y,z) <- meet]

-- (iv) if (x,y,z) in Meet and (u,x), (u,y) in LessThan, add (u,z) to LessThan
-- returns what should be added to <=
ruleFour :: [(String, String, String)] -> [(String, String)] -> [(String, String)]
ruleFour meet lessThan = [(u,z) | (x,y,z) <- meet, (u,x') <- lessThan,
                                                   (u',y') <- lessThan,
                                                   x == x', y == y', u == u']

-- (iii dual)
ruleThreeDual :: [(String, String, String)] -> [(String, String)]
ruleThreeDual join = nub $ [(x,z) | (x,y,z) <- join] ++ [(y,z) | (x,y,z) <- join]

-- (iv dual)
ruleFourDual :: [(String, String, String)] -> [(String, String)] -> [(String, String)]
ruleFourDual join lessThan = [(z,u) | (x,y,z) <- join, (x',u) <- lessThan,
                                                       (y',u') <- lessThan,
                                                        x == x', y == y', u == u']

-- closing under (i)-(iv), (iii dual), (iv dual)
-- returns new lessThan
closeOnce :: [String] -> [(String, String)] 
                      -> [(String, String, String)] 
                      -> [(String, String, String)]
                      -> [(String, String)]
closeOnce terms lessThan join meet = nub $ lessThan ++ reflexiveClosure terms
                                                    ++ transitiveClosure lessThan
                                                    ++ ruleThree meet
                                                    ++ ruleThreeDual join
                                                    ++ ruleFour meet lessThan 
                                                    ++ ruleFourDual join lessThan

-- input: hornFormula, output: closure of <=
closure :: [String] -> [(String, String)] 
                    -> [(String, String, String)] 
                    -> [(String, String, String)]
                    -> [(String, String)]
closure terms lessThan join meet
    | lessThan == tmpClosure = lessThan
    | otherwise              = closure terms tmpClosure join meet
    where tmpClosure = nub $ closeOnce terms lessThan join meet


-- input: hornFormula. closes lessThan
finalLessThan :: [(String, String)] -> [(String, String)]
finalLessThan hornFormula = closure terms (initialLessThan hornFormula) (initialJoin terms) (initialMeet terms)
    where terms = setOfSubterms hornFormula


-- input hornFormula
valid :: [(String, String)] -> Bool
valid hornFormula = (lastTuple `elem` lessThan) && ((snd lastTuple, fst lastTuple) `elem` lessThan)
    where lessThan  = finalLessThan hornFormula
          lastTuple = last hornFormula