inductive Color where
  | white
  | black
  deriving Repr, DecidableEq, Inhabited

def Color.opposite : Color → Color
  | white => black
  | black => white

inductive PieceType where
  | pawn | knight | bishop | rook | queen | king
  deriving Repr, DecidableEq

structure Piece where
  color : Color
  type  : PieceType
  deriving Repr, DecidableEq

abbrev File := Fin 8
abbrev Rank := Fin 8

structure Square where
  file : File
  rank : Rank
  deriving Repr, DecidableEq

/-- Board is defined as a function from `Square` to `Option Piece` -/
def Board := Square → Option Piece

/-- Empty board -/
def Board.empty : Board := fun _ => none

/-- Update a square on the board -/
def Board.update (b : Board) (sq : Square) (p : Option Piece) : Board :=
  fun s => if s == sq then p else b s
