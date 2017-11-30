module MNKGame

import Data.Vect
import Data.String

%default total


------ Types (and interfaces) ------

data Piece = X | O

Eq Piece where
  (==) X X = True
  (==) O O = True
  (==) _ _ = False

Show Piece where
  show X = "X"
  show O = "O"

Row : (m : Nat) -> Type
Row m = Vect m (Maybe Piece)

Board : (m, n : Nat) -> Type
Board m n = Vect n (Row m)


------ Display ------

showPiece : Maybe Piece -> String
showPiece Nothing = " "
showPiece (Just pce) = show pce

showRow : Row m -> String
showRow [] = "|"
showRow (x :: xs) = "| " ++ showPiece x ++ " " ++ showRow xs

showNumLabel : Nat -> String
showNumLabel k = let numLength = length $ unpack $ show k in
                     if numLength > 1
                        then show k
                        else " " ++ show k

joinStr : String -> Vect m Nat -> String
joinStr str [] = ""
joinStr str (x :: []) = showNumLabel x
joinStr str (x :: xs@(y :: ys)) = showNumLabel x ++ str ++ joinStr str xs

mLabelRow : (m : Nat) -> String
mLabelRow m = let leadingws = pack (List.replicate (3 + (List.length (unpack (show m)))) ' ')
                  mlist = reverse (genVect m) in
                  leadingws ++ (joinStr "  " mlist) ++ "\n"
  where
    genVect : (a : Nat) -> Vect a Nat
    genVect Z = []
    genVect (S b) = b :: genVect b

showBoard : Board m n -> String
showBoard {m} brd = mLabelRow m ++ showBoardHelper 0 brd ++ mLabelRow m
  where
    showBoardHelper : (a : Nat) -> Board m n -> String
    showBoardHelper a [] = ""
    showBoardHelper a (x :: xs) = showNumLabel a ++ " " ++ showRow x ++ " " ++
                                  showNumLabel a ++ "\n" ++ showBoardHelper (a + 1) xs


------ Proofs (and associated rewriting functions) ------

||| Defined here: http://docs.idris-lang.org/en/latest/tutorial/theorems.html
plusReducesS : (n : Nat) -> (m : Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S f) m = cong (plusReducesS f m)

plusSProof : Vect (plus k (S j)) elem -> Vect (S (plus k j)) elem
plusSProof {k} {j} xs = rewrite plusReducesS k j in xs

||| Proves that (a - b) + b = a
||| The LTE is necessary because of how Idris handles minus for Nats
plusMinusCancelOut : (a : Nat) -> (b : Nat) -> LTE b a -> plus b (minus a b) = a
plusMinusCancelOut Z Z LTEZero = Refl
plusMinusCancelOut (S k) Z LTEZero = Refl
plusMinusCancelOut (S right) (S left) (LTESucc x) = cong (plusMinusCancelOut right left x)

plusMinusProof : LTE b a -> Vect a elem -> Vect (plus b (minus a b)) elem
plusMinusProof {a} {b} prf xs = rewrite plusMinusCancelOut a b prf in xs


------ Gameplay functions ------

flipHorizontal : Board m n -> Board m n
flipHorizontal [] = []
flipHorizontal (x :: xs) = reverse x :: flipHorizontal xs

allRowEq : Row m -> Maybe Piece
allRowEq [] = Nothing
allRowEq (x :: []) = x
allRowEq (x :: xs@(y :: ys)) = case x of
                                    Nothing => Nothing
                                    (Just x') => if x == y
                                                    then allRowEq xs
                                                    else Nothing

||| Ported from Matrix library
deleteRow : Fin (S n) -> Board m (S n) -> Board m n
deleteRow = deleteAt

||| Ported from Matrix library
deleteCol : Fin (S m) -> Board (S m) n -> Board m n
deleteCol f = map (deleteAt f)

kSquare : (k : Nat) -> Board (k + mrest) (k + nrest) -> Board k k
kSquare k xs = map (take k) $ take k xs

kSquareList: (k : Nat) -> Board (k + mrest) (k + nrest) -> List (Board k k)
kSquareList {mrest = Z}     {nrest = Z}     k xs = [(kSquare k xs)]
kSquareList {mrest = (S j)} {nrest = Z} k xs = (kSquare k xs) ::
                                                   kSquareList {mrest = j} {nrest = Z}
                                                     k (deleteCol 0 (map plusSProof xs))
kSquareList {mrest = Z}     {nrest = (S i)}     k xs = (kSquare k xs) ::
                                                   kSquareList {mrest = Z} {nrest = i}
                                                     k (deleteRow 0 (plusSProof xs))
kSquareList {mrest = (S j)} {nrest = (S i)} k xs = (kSquare k xs) ::
                                                   kSquareList {mrest = (S j)} {nrest = i}
                                                     k (deleteRow 0 (plusSProof xs)) ++
                                                   kSquareList {mrest = j} {nrest = (S i)}
                                                     k (deleteCol 0 (map plusSProof xs))

diagsRowsCols : Board k k -> List (Row k)
diagsRowsCols xs = diag xs :: diag (flipHorizontal xs) ::
                   toList xs ++ toList (transpose xs)

allLines : (k : Nat) -> Board (k + mrest) (k + nrest) -> List (Row k)
allLines k xs = join $ map diagsRowsCols (kSquareList k xs)

||| If there any game winning lines, return that line's piece
anyWinningLines : (k : Nat) -> Board (k + mrest) (k + nrest) -> Maybe Piece
anyWinningLines Z xs = Nothing
anyWinningLines (S j) xs = checkLines (allLines (S j) xs)
  where
    checkLines : List (Row (S j)) -> Maybe Piece
    checkLines [] = Nothing
    checkLines (xxs@(x :: xs) :: ys) = case allRowEq xxs of
                                            Nothing => checkLines ys
                                            (Just x') => Just x'

replaceRow : Piece -> (x : Fin m) -> Row m -> Row m
replaceRow pce x row = replaceAt x (Just pce) row

addPiece' : Piece -> (x : Fin m) -> (y : Fin n) -> Board m n -> Board m n
addPiece' pce x FZ (z :: zs) = (replaceRow pce x z) :: zs
addPiece' pce x (FS y) (z :: zs) = z :: addPiece' pce x y zs

addPiece : Piece -> (x : Fin m) -> (y : Fin n) -> Board m n -> Maybe (Board m n)
addPiece pce x y brd = case index x $ index y brd of
                        Nothing => Just (addPiece' pce x y brd)
                        (Just pce') => Nothing

isDraw : Board m n -> Bool
isDraw {m} {n} brd = let (len ** flatboard) = catMaybes (concat brd) in
                         len == (m * n)

nextPiece : Piece -> Piece
nextPiece X = O
nextPiece O = X

emptyBoard : (m, n : Nat) -> Board m n
emptyBoard m n = replicate n (replicate m Nothing)

lteMNK : (m, n, k : Nat) -> Maybe (LTE k m, LTE k n)
lteMNK m n k = case isLTE k m of
                    (No contra) => Nothing
                    (Yes prfm) => case isLTE k n of
                                       (No contra) => Nothing
                                       (Yes prfn) => Just (prfm, prfn)


------ IO ------

partial
readVal : String -> IO Nat
readVal str =
  do putStr (str ++ ": ")
     testval <- getLine
     case parsePositive testval of
          Nothing => do putStrLn "Invalid value"
                        readVal str
          (Just val) => pure (cast val)

partial
readInput : String -> (bound : Nat) -> IO (Fin bound)
readInput str bound =
  do testval <- readVal str
     case natToFin testval bound of
          Nothing => do putStrLn "Out of range"
                        readInput str bound
          (Just val) => pure val

partial
gameLoop : (k : Nat) -> Board m n -> LTE k m -> LTE k n -> Piece -> IO ()
gameLoop {m} {n} k brd prfm prfn pce =
  do putStrLn (show pce ++ "'s turn")
     x <- readInput "x" m
     y <- readInput "y" n
     case addPiece pce x y brd of
          Nothing => do putStrLn "That space is occupied"
                        gameLoop k brd prfm prfn pce
          (Just newbrd) =>
            case (anyWinningLines
                   {mrest = m - k} {nrest = n - k} k
                   (plusMinusProof prfn
                     (map (plusMinusProof prfm) newbrd))) of
                 Nothing =>
                   if isDraw newbrd
                      then putStrLn "Draw"
                      else do putStrLn (showBoard newbrd)
                              gameLoop k newbrd prfm prfn (nextPiece pce)
                 (Just winpce) =>
                   do putStrLn (showBoard newbrd)
                      putStrLn ("Winner: " ++ (show winpce))
                      putStrLn ("Loser:  " ++ (show (nextPiece winpce)))

partial
enterValues : IO ()
enterValues =
  do putStrLn "Individually enter the m,n,k values"
     m <- readVal "m"
     n <- readVal "n"
     k <- readVal "k"
     case lteMNK m n k of
          Nothing => do putStrLn "k should not be larger than m or n"
                        enterValues
          (Just (prfm, prfn)) => do let firstboard = (emptyBoard m n)
                                    putStrLn (showBoard firstboard)
                                    gameLoop k firstboard prfm prfn X

partial
main : IO ()
main = do putStrLn "Welcome to MNK!"
          enterValues
