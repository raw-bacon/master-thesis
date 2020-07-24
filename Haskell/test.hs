

reverseString :: String -> String
reverseString [] = []
reverseString (x:xs) = (reverseString xs) ++ [x]


quickSort' ::  [Int] -> [Int]
quickSort' [] = []
quickSort' (x:[]) = [x]
quickSort' (x:xs) = quickSort' (filter (<=x) xs) ++ [x] ++ quickSort' (filter (>x) xs)