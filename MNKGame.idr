module MNKGame

import Data.Vect
import Data.String
import Control.ST

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
  show (MkRules False False False False) = "Normal"
  show (MkRules misere wild connectfour orderchaos)
    = (if misere then " Misere" else "") ++
      (if wild then " Wild" else "") ++
      (if connectfour then " ConnectFour" else "") ++
      (if orderchaos then " Order&Chaos" else "")

data Schema = SX
            | SY
            | SPiece
            | SP Piece
            | (.+.) Schema Schema

Show Schema where
  show SX = "Column"
  show SY = "Row"
  show SPiece = "Piece"
  show (SP pce) = "(" ++ show pce ++ ")"
  show (x .+. y) = show x ++ " " ++ show y

SchemaType : Schema -> (m, n : Nat) -> Type
SchemaType SX m n = Fin m
SchemaType SY m n = Fin n
SchemaType SPiece m n = Piece
SchemaType (SP pce) m n = Piece
SchemaType (left .+. right) m n = (SchemaType left m n, SchemaType right m n)

record Player where
  constructor MkPlayer
  name : String
  schema : Schema

Show Player where
  show (MkPlayer name schema) = name

record GameState where
  constructor MkGameState
  m : Nat
  n : Nat
  k : Nat
  board : Board m n
  rules : Rules
  player1 : Player
  player2 : Player
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
joinStr str (x :: xs) = showNumLabel x ++ str ++ joinStr str xs

mLabelRow : (m : Nat) -> String
mLabelRow m = let leadingws = pack (List.replicate (3 + (List.length (unpack (show m)))) ' ')
                  mlist = fromList $ take m [0..] in
                  leadingws ++ (joinStr "  " mlist) ++ "\n"

showBoard : Board m n -> String
showBoard {m} brd = mLabelRow m ++ showBoard' 0 brd ++ mLabelRow m
  where
    showBoard' : (a : Nat) -> Board m n -> String
    showBoard' a [] = ""
    showBoard' a (x :: xs) = showNumLabel a ++ " " ++ showRow x ++ " " ++
                             showNumLabel a ++ "\n" ++ showBoard' (a + 1) xs

||| Rework of unlines/unlines' for using chrs other than newlines
interleave : (c : Char) -> List String -> String
interleave c xs = pack $ interleave' $ map unpack xs
  where
    interleave' : List (List Char) -> List Char
    interleave' [] = []
    interleave' (l :: []) = l
    interleave' (l :: ls) = l ++ c :: interleave' ls

showRules : Rules -> String
showRules rules = "Rules: " ++ (interleave ',' $ words $ show rules)

showGame : GameState -> String
showGame (MkGameState m n k board rules p1 p2 prfm prfn)
  = "m,n,k = " ++ show m ++ "," ++ show n ++ "," ++ show k ++ ", " ++
    showRules rules ++ "\n" ++ showBoard board

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
diagsRowsCols xs = diag xs :: diag (map reverse xs) :: toList xs ++ toList (transpose xs)

allLines : (k : Nat) -> Board (k + mrest) (k + nrest) -> List (Row k)
allLines k xs = nub $ join $ map diagsRowsCols (kSquareList k xs)

allRowEq : Row m -> Bool
allRowEq [] = False
allRowEq (x :: []) = True
allRowEq (x :: xs@(y :: ys)) = if isJust x && x == y
                                  then allRowEq xs
                                  else False

||| If there any game winning lines, return that line's piece
anyWinningLines' : (k : Nat) -> Board (k + mrest) (k + nrest) -> Bool
anyWinningLines' Z xs = False
anyWinningLines' (S j) xs = checkLines (allLines (S j) xs)
  where
    checkLines : List (Row (S j)) -> Bool
    checkLines [] = False
    checkLines (x :: xs) = if allRowEq x then True else checkLines xs

anyWinningLines : (m, n, k : Nat) -> (newbrd : Board m n) ->
                  (prfm : LTE k m) -> (prfn : LTE k n) ->
                  Bool
anyWinningLines m n k newbrd prfm prfn
  = anyWinningLines' {mrest = m - k} {nrest = n - k}
                     k (plusMinusProof prfn (map (plusMinusProof prfm) newbrd))

addPiece' : Piece -> (x : Fin m) -> (y : Fin n) -> Board m n -> Board m n
addPiece' pce x FZ (z :: zs) = (replaceAt x (Just pce) z) :: zs
addPiece' pce x (FS y) (z :: zs) = z :: addPiece' pce x y zs

cfHelper : (n : Nat) -> Row a -> Maybe (Fin n)
cfHelper n {a = Z} [] = Nothing
cfHelper n {a = (S k)} (x :: xs)
  = case x of
         (Just pce') => cfHelper {a = k} n xs
         Nothing => natToFin k n

addPiece : SchemaType schema m n -> Board m n -> Maybe (Board m n)
addPiece {schema = (SX .+. SY .+. (SP _))}
         (x, (y, pce)) brd
  = case index x $ index y brd of
         Nothing => Just (addPiece' pce x y brd)
         (Just pce') => Nothing
addPiece {schema = (SX .+. (SP _))} {n}
         (x, pce) brd
  = do y <- cfHelper n $ reverse $ index x $ transpose brd
       Just (addPiece' pce x y brd)
addPiece {schema = (SX .+. SY .+. SPiece)}
         (x, (y, pce)) brd
  = case index x $ index y brd of
         Nothing => Just (addPiece' pce x y brd)
         (Just pce') => Nothing
addPiece {schema = (SX .+. SPiece)} {n}
         (x, pce) brd
  = do y <- cfHelper n $ reverse $ index x $ transpose brd
       Just (addPiece' pce x y brd)
addPiece {schema = _} _ _ = Nothing

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

createPlayers : (orderchaos, wild, connectfour : Bool) -> (Player, Player)
createPlayers True  _ False
  = ((MkPlayer "Order" (SX .+. SY .+. SPiece)),
     (MkPlayer "Chaos" (SX .+. SY .+. SPiece)))
createPlayers True  _ True
  = ((MkPlayer "Order" (SX .+. SPiece)),
     (MkPlayer "Chaos" (SX .+. SPiece)))
createPlayers False True False
  = ((MkPlayer "P1" (SX .+. SY .+. SPiece)),
     (MkPlayer "P2" (SX .+. SY .+. SPiece)))
createPlayers False True True
  = ((MkPlayer "P1" (SX .+. SPiece)),
     (MkPlayer "P2" (SX .+. SPiece)))
createPlayers False False False
  = ((MkPlayer "X" (SX .+. SY .+. (SP X))),
     (MkPlayer "O" (SX .+. SY .+. (SP O))))
createPlayers False False True
  = ((MkPlayer "X" (SX .+. (SP X))),
     (MkPlayer "O" (SX .+. (SP O))))

createPlayer1 : (orderchaos, wild, connectfour : Bool) -> Player
createPlayer1 True  _     False = (MkPlayer "Order" (SX .+. SY .+. SPiece))
createPlayer1 True  _     True = (MkPlayer "Order" (SX .+. SPiece))
createPlayer1 False True  False = (MkPlayer "P1" (SX .+. SY .+. SPiece))
createPlayer1 False True  True = (MkPlayer "P1" (SX .+. SPiece))
createPlayer1 False False False = (MkPlayer "X" (SX .+. SY .+. (SP X)))
createPlayer1 False False True = (MkPlayer "X" (SX .+. (SP X)))

createPlayer2 : (orderchaos, wild, connectfour : Bool) -> Player
createPlayer2 True  _     False = (MkPlayer "Chaos" (SX .+. SY .+. SPiece))
createPlayer2 True  _     True = (MkPlayer "Chaos" (SX .+. SPiece))
createPlayer2 False True  False = (MkPlayer "P2" (SX .+. SY .+. SPiece))
createPlayer2 False True  True = (MkPlayer "P2" (SX .+. SPiece))
createPlayer2 False False False = (MkPlayer "O" (SX .+. SY .+. (SP O)))
createPlayer2 False False True = (MkPlayer "O" (SX .+. (SP O)))

emptyBoard : (m, n : Nat) -> Board m n
emptyBoard m n = replicate n (replicate m Nothing)

lteMNK : (m, n, k : Nat) -> Maybe (LTE k m, LTE k n)
lteMNK m n k = case isLTE k m of
                    (No contra) => Nothing
                    (Yes prfm) => case isLTE k n of
                                       (No contra) => Nothing
                                       (Yes prfn) => Just (prfm, prfn)

createGameState : (m, n, k : Nat) -> (mis, wild, cf, oc : Bool) ->
                  (prfm : LTE k m) -> (prfn : LTE k n) ->
                  GameState
createGameState m n k mis wild cf oc prfm prfn =
       (MkGameState m n k
                    (emptyBoard m n)
                    (MkRules mis wild cf oc)
                    (createPlayer1 oc wild cf)
                    (createPlayer2 oc wild cf)
                    prfm prfn)

------ Save/Load ------
{-
savePiece : Maybe Piece -> String
savePiece Nothing = "-"
savePiece (Just pce) = show pce

saveBoard : Board m n -> String
saveBoard [] = ""
saveBoard (row :: rows) = (concat $ map savePiece row) ++ "\n" ++ saveBoard rows

saveGame' : GameState -> String
saveGame' (MkGameState {m} {n} board k rules (thisPlayer, nextPlayer) prfm prfn)
  = "m: " ++ show m ++ " , " ++ "n: " ++ show n ++ " , " ++ "k: " ++ show k ++ " , " ++
    showRules rules ++ " , " ++ "CurrentPlayer: " ++ show thisPlayer ++ "\n" ++
    saveBoard board

saveGame : (st : GameState) -> (filename : String) -> IO ()
saveGame st filename =
  do let gametxt = saveGame' st
     Right () <- writeFile filename gametxt
       | Left err => putStrLn (show err)
     pure ()

loadPiece : Char -> Maybe (Maybe Piece)
loadPiece 'X' = Just (Just X)
loadPiece 'O' = Just (Just O)
loadPiece '-' = Just Nothing
loadPiece _ = Nothing

loadRow : (m : Nat) -> String -> Maybe (Row m)
loadRow m str
  = let (row_len ** row) = catMaybes $ fromList $ map loadPiece $ unpack str in
        case decEq row_len m of
             (Yes Refl) => Just row
             (No contra) => Nothing

loadBoard : (m : Nat) -> (n : Nat) -> Vect n String -> (Maybe (Board m n))
loadBoard m n xs = let (n' ** board) = catMaybes $ map (loadRow m) xs in
                       case decEq n n' of
                            (Yes Refl) => Just board
                            (No contra) => Nothing

loadRules : String -> Maybe Rules
loadRules str = let xs = split (\c => c == ',') str in
                    Just (MkRules (elem "Misere" xs)
                                  ((elem "Wild" xs) || (elem "Order&Chaos" xs))
                                  (elem "ConnectFour" xs)
                                  (elem "Order&Chaos" xs))

loadPlayers : String -> (orderchaos, wild, connectfour : Bool) -> Maybe (Player, Player)
loadPlayers "X" False False False
  = Just ((MkPlayer "X" (SX .+. SY .+. (SP X))),
          (MkPlayer "O" (SX .+. SY .+. (SP O))))
loadPlayers "X" False False True
  = Just ((MkPlayer "X" (SX .+. (SP X))),
          (MkPlayer "O" (SX .+. (SP O))))
loadPlayers "O" False False False
  = Just ((MkPlayer "O" (SX .+. SY .+. (SP X))),
          (MkPlayer "X" (SX .+. SY .+. (SP O))))
loadPlayers "O" False False True
  = Just ((MkPlayer "O" (SX .+. (SP X))),
          (MkPlayer "X" (SX .+. (SP O))))
loadPlayers "P1" False True False
  = Just ((MkPlayer "P1" (SX .+. SY .+. SPiece)),
          (MkPlayer "P2" (SX .+. SY .+. SPiece)))
loadPlayers "P1" False True True
  = Just ((MkPlayer "P1" (SX .+. SPiece)),
          (MkPlayer "P2" (SX .+. SPiece)))
loadPlayers "P2" False True False
  = Just ((MkPlayer "P2" (SX .+. SY .+. SPiece)),
          (MkPlayer "P1" (SX .+. SY .+. SPiece)))
loadPlayers "P2" False True True
  = Just ((MkPlayer "P2" (SX .+. SPiece)),
          (MkPlayer "P1" (SX .+. SPiece)))
loadPlayers "Order" True _ False
  = Just ((MkPlayer "Order" (SX .+. SY .+. SPiece)),
          (MkPlayer "Chaos" (SX .+. SY .+. SPiece)))
loadPlayers "Order" True _ True
  = Just ((MkPlayer "Order" (SX .+. SPiece)),
          (MkPlayer "Chaos" (SX .+. SPiece)))
loadPlayers "Chaos" True _ False
  = Just ((MkPlayer "Chaos" (SX .+. SY .+. SPiece)),
          (MkPlayer "Order" (SX .+. SY .+. SPiece)))
loadPlayers "Chaos" True _ True
  = Just ((MkPlayer "Chaos" (SX .+. SPiece)),
          (MkPlayer "Order" (SX .+. SPiece)))
loadPlayers _ _ _ _ = Nothing

loadGame' : List String -> Maybe GameState
loadGame' ("m:" :: m_str :: "," ::
           "n:" :: n_str :: "," ::
           "k:" :: k_str :: "," ::
           "Rules:" :: rules_str :: "," ::
           "CurrentPlayer:" :: player_str ::
           board_list)
  = do m <- parsePositive {a = Nat} m_str
       n <- parsePositive {a = Nat} n_str
       k <- parsePositive {a = Nat} k_str
       (prfm, prfn) <- lteMNK m n k
       rules <- loadRules rules_str
       players <- loadPlayers player_str (orderchaos rules) (wild rules) (connectfour rules)
       board_vect <- exactLength n (fromList board_list)
       board <- loadBoard m n board_vect
       Just (MkGameState board k rules players prfm prfn)
loadGame' _ = Nothing

loadGame : (filename : String) -> IO (Either String GameState)
loadGame filename =
  do Right contents <- readFile filename
       | Left err => pure (Left (show err))
     case loadGame' (words contents) of
          Nothing => pure (Left "Game file in incorrect format")
          Just st => pure (Right st)

load : IO ()
load = do putStr "Input filename with saved game: "
          f <- getLine
          Right st <- loadGame f
            | Left err_str => putStrLn err_str
          putStrLn (showGame st)
-}
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
parsePrefix (SP pce) input m n = Just (pce, "")
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

parseRules : List String -> Vect 4 Bool
parseRules xs = [elem "mis" xs,
                 (elem "wild" xs) || (elem "oc" xs),
                 elem "cf" xs,
                 elem "oc" xs]

parseNewGame : List String -> Maybe (Vect 3 Nat, Vect 4 Bool)
parseNewGame (m_str :: n_str :: k_str :: rules_str)
  = do m <- parsePositive {a = Nat} m_str
       n <- parsePositive {a = Nat} n_str
       k <- parsePositive {a = Nat} k_str
       Just ([m, n, k], parseRules rules_str)
parseNewGame _ = Nothing

------ IO ------

createNewGame : String -> Either String GameState
createNewGame testvals
  = case parseNewGame (words testvals) of
         Nothing => Left "Invalid input"
         Just ([m, n, k], [mis, wild, cf, oc]) =>
           case lteMNK m n k of
                Nothing => Left "k should not be larger than m or n"
                Just (prfm, prfn) =>
                  Right (createGameState m n k mis wild cf oc prfm prfn)

data MoveResult = Continue | InvalidMove | SpaceOccupied | KLine | BoardFilled

data GameEnder : MoveResult -> Type where
     KLineEnd : GameEnder KLine
     BoardFilledEnd : GameEnder BoardFilled

data GameResult = P1Win | P2Win | Draw

Show GameResult where
  show P1Win = "Player1 is the winner!"
  show P2Win = "Player2 is the winner!"
  show Draw = "It's a draw. No winner!"

data MenuInput = NewGame | ExitMenu | InvalidMCmd

data AppState = InMenu | P1Turn | P2Turn | GameOver

data InGame : AppState -> Type where
     P1Now : InGame P1Turn
     P2Now : InGame P2Turn

nextTurn : {auto prf : InGame st} -> (st : AppState) -> AppState
nextTurn {prf = P1Now} st = P2Turn
nextTurn {prf = P2Now} st = P1Turn

interface CLIApp (m : Type -> Type) where
  AS : AppState -> Type

  launch : ST m Var [add (AS InMenu)]
  exit : (as : Var) -> ST m () [remove as (AS InMenu)]

  menuInput : (as : Var) -> String ->
              ST m MenuInput [as ::: (AS InMenu) :->
                                     (\res => AS (case res of
                                                       NewGame => P1Turn
                                                       ExitMenu => InMenu
                                                       InvalidMCmd => InMenu))]

  makeMoveP1 : (as : Var) ->
               ST m MoveResult [as ::: (AS P1Turn) :->
                                       (\res => AS (case res of
                                                         Continue => P2Turn
                                                         InvalidMove => P1Turn
                                                         SpaceOccupied => P1Turn
                                                         KLine => GameOver
                                                         BoardFilled => GameOver))]
  makeMoveP2 : (as : Var) ->
               ST m MoveResult [as ::: (AS P2Turn) :->
                                       (\res => AS (case res of
                                                         Continue => P1Turn
                                                         InvalidMove => P2Turn
                                                         SpaceOccupied => P2Turn
                                                         KLine => GameOver
                                                         BoardFilled => GameOver))]

  displayGame : (as : Var) -> {auto prf : InGame st} ->
                ST m () [as ::: (AS st)]

  displayScore : (as : Var) -> ST m () [as ::: (AS InMenu)]

  endMessage : (as : Var) ->
               {auto lastturn : InGame st} -> {auto ender : GameEnder move} ->
               ST m GameResult [as ::: (AS GameOver)]
  endGame : (as : Var) -> GameResult ->
            ST m () [as ::: (AS GameOver) :-> (AS InMenu)]

ConsoleIO io => CLIApp io where
  AS InMenu = Composite [State Nat, State Nat, State Nat]
  AS P1Turn = Composite [State Nat, State Nat, State Nat, State GameState]
  AS P2Turn = Composite [State Nat, State Nat, State Nat, State GameState]
  AS GameOver = Composite [State Nat, State Nat, State Nat, State GameState]

  launch = do as <- new ()
              p1wins <- new 0
              p2wins <- new 0
              draws <- new 0
              combine as [p1wins, p2wins, draws]
              pure as
  exit as = do [p1wins, p2wins, draws] <- split as
               delete p1wins
               delete p2wins
               delete draws
               delete as

  menuInput as "exit" = pure ExitMenu
  menuInput as str =
    case createNewGame str of
         (Left err) => do putStrLn err; pure InvalidMCmd
         (Right gs) =>
           do [p1wins, p2wins, draws] <- split as
              gsvar <- new gs
              combine as [p1wins, p2wins, draws, gsvar]
              pure NewGame

  makeMoveP1 as =
    do [p1wins, p2wins, draws, gsvar] <- split as
       (MkGameState m n k board rules p1 p2 prfm prfn) <- read gsvar
       let schema = schema p1
       putStrLn "P1's Turn"
       putStr (show schema ++ ": ")
       testinput <- getStr
       case parseBySchema schema testinput m n of
            Nothing => do combine as [p1wins, p2wins, draws, gsvar]
                          pure InvalidMove
            (Just validinput) =>
              case addPiece validinput board of
                   Nothing => do combine as [p1wins, p2wins, draws, gsvar]
                                 pure SpaceOccupied
                   (Just newbrd) =>
                     do write gsvar (MkGameState m n k newbrd rules p1 p2 prfm prfn)
                        combine as [p1wins, p2wins, draws, gsvar]
                        if anyWinningLines m n k newbrd prfm prfn
                           then pure KLine
                        else if isBoardFull newbrd
                                then pure BoardFilled
                                else pure Continue
  makeMoveP2 as =
    do [p1wins, p2wins, draws, gsvar] <- split as
       (MkGameState m n k board rules p1 p2 prfm prfn) <- read gsvar
       let schema = schema p2
       putStrLn "P2's Turn"
       putStr (show schema ++ ": ")
       testinput <- getStr
       case parseBySchema schema testinput m n of
            Nothing => do combine as [p1wins, p2wins, draws, gsvar]
                          pure InvalidMove
            (Just validinput) =>
              case addPiece validinput board of
                   Nothing => do combine as [p1wins, p2wins, draws, gsvar]
                                 pure SpaceOccupied
                   (Just newbrd) =>
                     do write gsvar (MkGameState m n k newbrd rules p1 p2 prfm prfn)
                        combine as [p1wins, p2wins, draws, gsvar]
                        if anyWinningLines m n k newbrd prfm prfn
                           then pure KLine
                        else if isBoardFull newbrd
                                then pure BoardFilled
                                else pure Continue

  displayGame {prf = P1Now} as =
    do [p1wins, p2wins, draws, gsvar] <- split as
       gs <- read gsvar
       putStrLn $ showGame gs
       combine as [p1wins, p2wins, draws, gsvar]
  displayGame {prf = P2Now} as =
    do [p1wins, p2wins, draws, gsvar] <- split as
       gs <- read gsvar
       putStrLn $ showGame gs
       combine as [p1wins, p2wins, draws, gsvar]

  displayScore as =
    do [p1wins, p2wins, draws] <- split as
       p1 <- read p1wins
       p2 <- read p2wins
       d <- read draws
       putStrLn $ "Current score:\n" ++
                  "  P1 wins : " ++ show p1 ++ "\n" ++
                  "  P2 wins : " ++ show p2 ++ "\n" ++
                  "  Draws :   " ++ show d
       combine as [p1wins, p2wins, draws]

  endMessage {lastturn = P1Now} {ender = KLineEnd} as
    = do [p1wins, p2wins, draws, gsvar] <- split as
         gs <- read gsvar
         combine as [p1wins, p2wins, draws, gsvar]
         let mis = misere $ rules gs
         let oc = orderchaos $ rules gs
         if mis then pure P2Win
                else pure P1Win
  endMessage {lastturn = P2Now} {ender = KLineEnd} as
    = do [p1wins, p2wins, draws, gsvar] <- split as
         gs <- read gsvar
         combine as [p1wins, p2wins, draws, gsvar]
         let mis = misere $ rules gs
         let oc = orderchaos $ rules gs
         if oc then if mis then pure P2Win
                           else pure P1Win
               else if mis then pure P1Win
                           else pure P2Win
  endMessage {lastturn = _} {ender = BoardFilledEnd} as
    = do [p1wins, p2wins, draws, gsvar] <- split as
         gs <- read gsvar
         combine as [p1wins, p2wins, draws, gsvar]
         let mis = misere $ rules gs
         let oc = orderchaos $ rules gs
         if oc then if mis then pure P1Win
                           else pure P2Win
               else pure Draw

  endGame as P1Win
    = do [p1wins, p2wins, draws, gsvar] <- split as
         delete gsvar
         update p1wins (+1)
         combine as [p1wins, p2wins, draws]
  endGame as P2Win
    = do [p1wins, p2wins, draws, gsvar] <- split as
         delete gsvar
         update p2wins (+1)
         combine as [p1wins, p2wins, draws]
  endGame as Draw
    = do [p1wins, p2wins, draws, gsvar] <- split as
         delete gsvar
         update draws (+1)
         combine as [p1wins, p2wins, draws]

%default partial

using (ConsoleIO io, CLIApp io)
  gameLoop : (as : Var) -> {auto prf : InGame st} ->
             ST io () [as ::: (AS {m=io} st) :-> (AS {m=io} InMenu)]
  gameLoop {prf = P1Now} as = do displayGame as
                                 moveresult <- makeMoveP1 as
                                 case moveresult of
                                      Continue => gameLoop as
                                      InvalidMove =>
                                        do putStrLn "Invalid input"
                                           gameLoop as
                                      SpaceOccupied =>
                                        do putStrLn "Space occupied"
                                           gameLoop as
                                      KLine =>
                                        do result <- endMessage as
                                           printLn result
                                           endGame as result
                                      BoardFilled =>
                                        do result <- endMessage as
                                           printLn result
                                           endGame as result
  gameLoop {prf = P2Now} as = do displayGame as
                                 moveresult <- makeMoveP2 as
                                 case moveresult of
                                      Continue => gameLoop as
                                      InvalidMove =>
                                        do putStrLn "Invalid input"
                                           gameLoop as
                                      SpaceOccupied =>
                                        do putStrLn "Space occupied"
                                           gameLoop as
                                      KLine =>
                                        do result <- endMessage as
                                           printLn result
                                           endGame as result
                                      BoardFilled =>
                                        do result <- endMessage as
                                           printLn result
                                           endGame as result

  menuLoop : (as : Var) -> ST io () [as ::: (AS {m=io} InMenu)]
  menuLoop as = do putStr "Enter game values (or 'exit' to close app): "
                   input <- getStr
                   mi <- menuInput as input
                   case mi of
                        ExitMenu => putStrLn "Thanks for playing"
                        InvalidMCmd => menuLoop as
                        NewGame => do gameLoop as
                                      displayScore as
                                      menuLoop as

  startApp : ST io () []
  startApp = do putStrLn "Welcome to MNK!"
                putStrLn ("Optional game modes:\n" ++
                          "  mis (Misère): Usual winner and loser are reversed\n" ++
                          "  wild (Wild): Both players can use X or O\n" ++
                          "  cf (ConnectFour): Player's piece will go to the lowest\n" ++
                          "                    position in the selected column\n" ++
                          "  oc (Order&Chaos): 1st player (Order) tries to make a\n" ++
                          "                    k-length row, while 2nd player (Chaos)\n" ++
                          "                    tries to prevent this")
                as <- launch
                call (menuLoop as)
                exit as

main : IO ()
main = run startApp

-- Local Variables:
-- idris-load-packages: ("prelude" "contrib" "base")
-- End:
