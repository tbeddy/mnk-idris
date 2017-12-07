# mnk-idris

This is a small personal project to learn the dependently-typed language [Idris](http://idris-lang.org/) while going through the book [Type-Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris). It's a work in progress, so expect breaking changes.

This project implements a CLI [m,n,k-game](https://en.wikipedia.org/wiki/M,n,k-game). Several variations can be selected when starting a new game: [Misère](https://en.wikipedia.org/wiki/Tic-tac-toe_variants#Mis.C3.A8re_games), [Connect Four](https://en.wikipedia.org/wiki/Connect_Four) input, [Wild (Tic Tac Toe)](https://en.wikipedia.org/wiki/Wild_tic-tac-toe), and [Order&Chaos](https://en.wikipedia.org/wiki/Order_and_Chaos).

For example, if you want to play an 8,5,4 game with Misère, Connect Four, Wild, and Order&Chaos all turned on, enter your terminal:
```
cd mnk-idris
idris MNKGame.idr
*MNKGame> :exec main
Welcome to MNK!
Enter m,n,k values and any extra game modes: 8 5 4 mis cf wild oc
Rules: Misere Wild ConnectFour Order&Chaos
     0   1   2   3   4   5   6   7
 0 |   |   |   |   |   |   |   |   |  0
 1 |   |   |   |   |   |   |   |   |  1
 2 |   |   |   |   |   |   |   |   |  2
 3 |   |   |   |   |   |   |   |   |  3
 4 |   |   |   |   |   |   |   |   |  4
     0   1   2   3   4   5   6   7

Order's turn
X-coordinate Piece: 3 X
```

After a while...

```
Order's turn
X-coordinate Piece: 6 X
     0   1   2   3   4   5   6   7
 0 |   |   |   |   |   |   |   |   |  0
 1 |   |   |   |   |   |   | X |   |  1
 2 |   |   |   |   |   | X | O |   |  2
 3 |   | X |   |   | X | O | X |   |  3
 4 |   | X | O | X | O | O | O |   |  4
     0   1   2   3   4   5   6   7

Winner: Chaos
Loser:  Order
```