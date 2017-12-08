module MNKGame

import Data.Vect
import Data.String

%default total

infixr 5 .+.

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

record Rules where
  constructor MkRules
  misere : Bool
  wild : Bool
  connectfour : Bool
  orderchaos : Bool

Show Rules where
  show (MkRules False False False False) = "Rules: Normal"
  show (MkRules misere wild connectfour orderchaos)
    = "Rules:" ++
      (if misere then " Misere" else "") ++
      (if wild then " Wild" else "") ++
      (if connectfour then " ConnectFour" else "") ++
      (if orderchaos then " Order&Chaos" else "")

record Player where
  constructor MkPlayer
  name : String
  pieces : Piece

Show Player where
  show (MkPlayer name pieces) = name

data Schema = SX
            | SY
            | SPiece
            | (.+.) Schema Schema

Show Schema where
  show SX = "Column"
  show SY = "Row"
  show SPiece = "Piece"
  show (x .+. y) = show x ++ " " ++ show y

SchemaType : Schema -> (m, n : Nat) -> Type
SchemaType SX m n = Fin m
SchemaType SY m n = Fin n
SchemaType SPiece m n = Piece
SchemaType (left .+. right) m n = (SchemaType left m n, SchemaType right m n)

record Game where
  constructor MkGame
  board : Board m n
  k : Nat
  rules : Rules
  schema : Schema
  players : (Player, Player)
  prfm : LTE k m
  prfn : LTE k n

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

showGame : Game -> String
showGame (MkGame board k rules schema players prfm prfn)
  = "k = " ++ show k ++ ", " ++ show rules ++ "\n" ++ showBoard board

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
kSquareList {mrest = (S j)} {nrest = Z}     k xs = (kSquare k xs) ::
                                                   kSquareList {mrest = j} {nrest = Z}
                                                     k (deleteCol 0 (map plusSProof xs))
kSquareList {mrest = Z}     {nrest = (S i)} k xs = (kSquare k xs) ::
                                                   kSquareList {mrest = Z} {nrest = i}
                                                     k (deleteRow 0 (plusSProof xs))
kSquareList {mrest = (S j)} {nrest = (S i)} k xs = (kSquare k xs) ::
                                                   kSquareList {mrest = (S j)} {nrest = i}
                                                     k (deleteRow 0 (plusSProof xs)) ++
                                                   kSquareList {mrest = j} {nrest = (S i)}
                                                     k (deleteCol 0 (map plusSProof xs))

diagsRowsCols : Board k k -> List (Row k)
diagsRowsCols xs = diag xs :: diag (map reverse xs) ::
                   toList xs ++ toList (transpose xs)

allLines : (k : Nat) -> Board (k + mrest) (k + nrest) -> List (Row k)
allLines k xs = join $ map diagsRowsCols (kSquareList k xs)

allRowEq : Row m -> Maybe Piece
allRowEq [] = Nothing
allRowEq (x :: []) = x
allRowEq (x :: xs@(y :: ys)) = case x of
                                    Nothing => Nothing
                                    (Just x') => if x == y
                                                    then allRowEq xs
                                                    else Nothing

||| If there any game winning lines, return that line's piece
anyWinningLines : (k : Nat) -> Board (k + mrest) (k + nrest) -> Maybe Piece
anyWinningLines Z xs = Nothing
anyWinningLines (S j) xs = checkLines (allLines (S j) xs)
  where
    checkLines : List (Row (S j)) -> Maybe Piece
    checkLines [] = Nothing
    checkLines (x :: xs) = case allRowEq x of
                                Nothing => checkLines xs
                                (Just x') => Just x'

addPiece' : Piece -> (x : Fin m) -> (y : Fin n) -> Board m n -> Board m n
addPiece' pce x FZ (z :: zs) = (replaceAt x (Just pce) z) :: zs
addPiece' pce x (FS y) (z :: zs) = z :: addPiece' pce x y zs

cfHelper : Row a -> Maybe Nat
cfHelper {a = Z} [] = Nothing
cfHelper {a = (S k)} (x :: xs)
  = case x of
         Nothing => Just k
         (Just pce') => cfHelper {a = k} xs

addPiece : SchemaType schema m n -> Board m n -> Player -> Maybe (Board m n)
addPiece {schema = (SX .+. SY)}
         (x, y) brd plyr
  = case index x $ index y brd of
         Nothing => Just (addPiece' (pieces plyr) x y brd)
         (Just pce') => Nothing
addPiece {schema = SX} {n}
         x brd plyr
  = do y' <- cfHelper (reverse $ index x $ transpose brd)
       y <- natToFin y' n
       Just (addPiece' (pieces plyr) x y brd)
addPiece {schema = (SX .+. SY .+. SPiece)}
         (x, (y, pce)) brd plyr
  = case index x $ index y brd of
         Nothing => Just (addPiece' pce x y brd)
         (Just pce') => Nothing
addPiece {schema = (SX .+. SPiece)} {n}
         (x, pce) brd plyr
  = do y' <- cfHelper (reverse $ index x $ transpose brd)
       y <- natToFin y' n
       Just (addPiece' pce x y brd)
addPiece {schema = _} schtype brd plyr = Nothing

------ Game ending ------

isBoardFull : Board m n -> Bool
isBoardFull {m} {n} brd = let (len ** _) = catMaybes (concat brd) in
                              len == (m * n)

showWinnerAndLoser : (winner, loser : String) -> String
showWinnerAndLoser winner loser = "Winner: " ++ winner ++ "\nLoser:  " ++ loser

fullBoardEnding : (orderchaos : Bool) -> String
fullBoardEnding False = "Draw"
fullBoardEnding True = showWinnerAndLoser "Chaos" "Order"

winningLineEnding : (p1, p2 : Player) -> (misere, orderchaos : Bool) -> String
winningLineEnding p1 p2 False False
  = showWinnerAndLoser (show p1) (show p2)
winningLineEnding p1 p2 False True
  = showWinnerAndLoser "Order" "Chaos"
winningLineEnding p1 p2 True False
  = showWinnerAndLoser (show p2) (show p1)
winningLineEnding p1 p2 True True
  = showWinnerAndLoser "Chaos" "Order"

------ Game initialization ------

createSchema : (wild, connectfour : Bool) -> Schema
createSchema False False = (SX .+. SY)
createSchema False True = SX
createSchema True False = (SX .+. SY .+. SPiece)
createSchema True True = (SX .+. SPiece)

createPlayers : (wild, orderchaos : Bool) -> (Player, Player)
createPlayers _    True = ((MkPlayer "Order" X), (MkPlayer "Chaos" O))
createPlayers True _    = ((MkPlayer "P1" X), (MkPlayer "P2" O))
createPlayers _    _    = ((MkPlayer "X" X), (MkPlayer "O" O))

emptyBoard : (m, n : Nat) -> Board m n
emptyBoard m n = replicate n (replicate m Nothing)

lteMNK : (m, n, k : Nat) -> Maybe (LTE k m, LTE k n)
lteMNK m n k = case isLTE k m of
                    (No contra) => Nothing
                    (Yes prfm) => case isLTE k n of
                                       (No contra) => Nothing
                                       (Yes prfn) => Just (prfm, prfn)

------ Input parsing ------

parsePrefix : (schema : Schema) -> String -> (m, n : Nat) ->
              Maybe (SchemaType schema m n, String)
parsePrefix SX input m n
  = case span isDigit input of
         ("", rest) => Nothing
         (testnum, rest) =>
           do testnat <- parsePositive {a = Nat} testnum
              x <- natToFin testnat m
              Just (x, ltrim rest)
parsePrefix SY input m n
  = case span isDigit input of
         ("", rest) => Nothing
         (testnum, rest) =>
           do testnat <- parsePositive {a = Nat} testnum
              y <- natToFin testnat n
              Just (y, ltrim rest)
parsePrefix SPiece input m n = maybePieceInput (unpack input)
  where
    maybePieceInput : List Char -> Maybe (Piece, String)
    maybePieceInput ('X' :: rest) = Just (X, ltrim (pack rest))
    maybePieceInput ('O' :: rest) = Just (O, ltrim (pack rest))
    maybePieceInput _ = Nothing
parsePrefix (left .+. right) input m n =
  do (l_val, input') <- parsePrefix left input m n
     (r_val, input'') <- parsePrefix right input' m n
     Just ((l_val, r_val), input'')

parseBySchema : (schema : Schema) -> String -> (m, n : Nat) ->
                Maybe (SchemaType schema m n)
parseBySchema schema input m n = case parsePrefix schema input m n of
                                      (Just (res, "")) => Just res
                                      (Just _) => Nothing
                                      Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("X" :: xs)
  = case xs of
         [] => Just SX
         _ => case parseSchema xs of
                   Nothing => Nothing
                   (Just xs_sch) => Just (SX .+. xs_sch)
parseSchema ("Y" :: xs)
  = case xs of
         [] => Just SY
         _ => case parseSchema xs of
                   Nothing => Nothing
                   (Just xs_sch) => Just (SY .+. xs_sch)
parseSchema ("Piece" :: xs)
  = case xs of
         [] => Just SPiece
         _ => case parseSchema xs of
                   Nothing => Nothing
                   (Just xs_sch) => Just (SPiece .+. xs_sch)
parseSchema _ = Nothing

parseRules : List String -> Vect 4 Bool
parseRules xs = [elem "mis" xs,
                 elem "wild" xs,
                 elem "cf" xs,
                 elem "oc" xs]

parseNewGame : List String -> Maybe (Vect 3 Nat, Vect 4 Bool)
parseNewGame xs = let (_ ** mnkvals) = catMaybes $ fromList $
                                       map (parsePositive {a = Nat}) $ take 3 xs
                      rules = drop 3 xs in
                      case exactLength 3 mnkvals of
                           Nothing => Nothing
                           (Just mnkvals') => Just (mnkvals', parseRules rules)

------ IO ------

partial
gameLoop : Game -> IO ()
gameLoop st@(MkGame {m} {n} board k rules schema (thisPlayer, nextPlayer) prfm prfn) =
  do putStrLn ((show thisPlayer) ++ "'s turn")
     putStr (show schema ++ ": ")
     testinput <- getLine
     case parseBySchema schema testinput m n of
          Nothing => do putStrLn "Invalid input"
                        gameLoop st
          (Just validinput) =>
            case addPiece validinput board thisPlayer of
                 Nothing => do putStrLn "That space is occupied"
                               gameLoop st
                 (Just newbrd) =>
                   case (anyWinningLines {mrest = m - k} {nrest = n - k}
                          k (plusMinusProof prfn (map (plusMinusProof prfm) newbrd))) of
                        Nothing =>
                          if isBoardFull newbrd
                             then putStrLn $ fullBoardEnding $ orderchaos rules
                             else do let newgamestate = (MkGame newbrd k rules schema
                                                                (nextPlayer, thisPlayer)
                                                                prfm prfn)
                                     putStrLn (showGame newgamestate)
                                     gameLoop newgamestate
                        (Just winpce) =>
                          do putStrLn (showBoard newbrd)
                             putStrLn (winningLineEnding
                                        thisPlayer nextPlayer
                                        (misere rules) (orderchaos rules))

partial
enterValues : IO ()
enterValues =
  do putStr "Enter m,n,k values and any extra game modes (all separated by spaces): "
     testvals <- getLine
     case parseNewGame (words testvals) of
          Nothing => do putStrLn "Invalid input"
                        enterValues
          (Just ([m, n, k], [mis, wild, cf, oc])) =>
            case lteMNK m n k of
                 Nothing => do putStrLn "k should not be larger than m or n"
                               enterValues
                 (Just (prfm, prfn)) =>
                   do let initialgame = (MkGame (emptyBoard m n) k
                                                (MkRules mis wild cf oc)
                                                (createSchema wild cf)
                                                (createPlayers wild oc)
                                                prfm prfn)
                      putStrLn (showGame initialgame)
                      gameLoop initialgame

partial
main : IO ()
main = do putStrLn "Welcome to MNK!"
          putStrLn ("Optional game modes:\n" ++
                    "  mis (Misère): Usual winner and loser are reversed\n" ++
                    "  wild (Wild): Both players can use X or O\n" ++
                    "  cf (ConnectFour): Player's piece will go to the lowest\n" ++
                    "                    position in the selected column\n" ++
                    "  oc (Order&Chaos): 1st player (Order) tries to make a\n" ++
                    "                    k-length row, while 2nd player (Chaos)\n" ++
                    "                    tries to prevent this")
          enterValues
