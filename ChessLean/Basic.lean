/-
Authors: Malhar A. Patel
-/

inductive Color where
  | white
  | black
  deriving Repr, Inhabited, DecidableEq

def Color.opposite : Color → Color
  | white => black
  | black => white

inductive PieceType where
  | pawn | knight | bishop | rook | queen | king
  deriving Repr, Inhabited, DecidableEq

structure Piece where
  color : Color
  type  : PieceType
  deriving Repr, Inhabited, DecidableEq

abbrev File := Fin 8
abbrev Rank := Fin 8

structure Square where
  file : File
  rank : Rank
  deriving Repr, Inhabited, DecidableEq

/-- Board is defined as a function from `Square` to `Option Piece` -/
def Board := Square → Option Piece

/-- Empty board -/
def Board.empty : Board := fun _ => none

/-- Update a square on the board -/
def Board.update (b : Board) (sq : Square) (p : Option Piece) : Board :=
  fun s => if s == sq then p else b s

def Board.start : Board := fun ⟨file, rank⟩ =>
  match rank.val with
  | 1 => some ⟨.white, .pawn⟩
  | 6 => some ⟨.black, .pawn⟩
  | 0 => backRank .white file.val
  | 7 => backRank .black file.val
  | _ => none
where
  backRank (c : Color) (f : Nat) : Option Piece :=
    match f with
    | 0 | 7 => some ⟨c, .rook⟩
    | 1 | 6 => some ⟨c, .knight⟩
    | 2 | 5 => some ⟨c, .bishop⟩
    | 3     => some ⟨c, .queen⟩
    | 4     => some ⟨c, .king⟩
    | _     => none

def Piece.toUnicode : Piece → String
  | ⟨.white, .pawn⟩   => "♟"
  | ⟨.white, .knight⟩ => "♞"
  | ⟨.white, .bishop⟩ => "♝"
  | ⟨.white, .rook⟩   => "♜"
  | ⟨.white, .queen⟩  => "♛"
  | ⟨.white, .king⟩   => "♚"
  | ⟨.black, .pawn⟩   => "♙"
  | ⟨.black, .knight⟩ => "♘"
  | ⟨.black, .bishop⟩ => "♗"
  | ⟨.black, .rook⟩   => "♖"
  | ⟨.black, .queen⟩  => "♕"
  | ⟨.black, .king⟩   => "♔"

instance : Repr Board where
  reprPrec b _ :=
    let ranks : List (Fin 8) := [7, 6, 5, 4, 3, 2, 1, 0]
    let files : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

    let boardLines := ranks.map fun r =>
      let rowPieces := files.map fun f =>
        match b ⟨f, r⟩ with
        | none   => "・"
        | some p => p.toUnicode
      let rowStr := String.intercalate " " rowPieces
      s!"{r.val + 1} | {rowStr} |"

    let border := "  +-----------------+"
    let footer := "    a b c d e f g h"
    let lines  := [border] ++ boardLines ++ [border, footer]
    Std.Format.text (String.intercalate "\n" lines)

#eval Board.start

instance : Inhabited Board where
  default := .start

structure NormalMove where
  fromSq : Square
  toSq   : Square
  deriving Repr, Inhabited, DecidableEq

structure PawnPromotionMove where
  fromSq    : Square
  toSq      : Square
  promotion : PieceType
  deriving Repr, Inhabited, DecidableEq

structure PawnEnPassantMove where
  fromSq      : Square
  enPassantSq : Square
  deriving Repr, Inhabited, DecidableEq

inductive Castle where
  | kingside
  | queenside
  deriving Repr, Inhabited, DecidableEq

structure CastlingRights where
  whiteKingside  : Bool := true
  whiteQueenside : Bool := true
  blackKingside  : Bool := true
  blackQueenside : Bool := true
  deriving Repr, Inhabited, DecidableEq

inductive Move where
  | normal    (m : NormalMove)
  | castle    (m : Castle)
  | promotion (m : PawnPromotionMove)
  | enPassant (m : PawnEnPassantMove)
  deriving Repr, Inhabited, DecidableEq

#check Char.toNat
#eval Char.toNat 'a'

#check Fin 8

def cF (ch : Char) : File :=
  let n := ch.toNat - 97
  if h : n < 8 then ⟨n, h⟩
  else 7

def nR (n : Nat) : Rank :=
  if h : n < 8 then ⟨n - 1, by grind⟩
  else 7

syntax "n'[" term "," term "," term "," term "]" : term
macro_rules
  | `(n'[ $c1:term , $n1:term, $c2:term , $n2:term ]) =>
    `(Move.normal ⟨ ⟨ cF $c1 , nR $n1 ⟩, ⟨ cF $c2 , nR $n2 ⟩ ⟩)

syntax "n[" term "," term "," term "," term "]" : term
macro_rules
  | `(n[ $c1:term , $n1:term, $c2:term , $n2:term ]) =>
    `(Move.normal ⟨ ⟨ nR $c1 , nR $n1 ⟩, ⟨ nR $c2 , nR $n2 ⟩ ⟩)

syntax "O-O" : term
macro_rules
  | `(O-O) => `(Move.castle Castle.kingside)

syntax "O-O-O" : term
macro_rules
  | `(O-O-O) => `(Move.castle Castle.queenside)

syntax "p[" term "," term "," term "," term "," term "]" : term
macro_rules
  | `(p[ $c1:term , $n1:term, $c2:term , $n2:term , $p:term]) =>
    `(Move.promotion ⟨ ⟨ nR $c1 , nR $n1 ⟩, ⟨ nR $c2 , nR $n2 ⟩, $p ⟩)

#eval O-O-O

#eval n'['e', 2, 'e', 5]

#eval p[2, 2, 3, 5, PieceType.queen]

-- notation "n[" ch1 "," num1 "," ch2 "," num2 "]" =>
--   Move.normal ⟨charToFile ch1, numToRank num1⟩

inductive Result where
  | ongoing
  | win (col : Color)
  | draw
  deriving Repr, Inhabited, DecidableEq

structure Captures where
  white : List Piece
  black : List Piece
  deriving Repr, Inhabited, DecidableEq

structure GameState where
  board       : Board := .start
  turn        : Color := .white
  castling    : CastlingRights := {}
  enPassantSq : Option Square := none
  captures    : Captures := ⟨ [], [] ⟩
  halfMoves   : Nat := 0
  numMove     : Nat := 0
  result      : Result := .ongoing
  valid       : Bool := true
  messages    : List String := []
  history     : List Move := []

instance : Inhabited GameState where
  default := {
    board := default
    turn := .white
    castling := {}
    enPassantSq := none
    captures := ⟨ [], [] ⟩
    halfMoves := 0
    numMove := 0
    result := .ongoing
    valid := true
    messages := []
    history := []
  }

instance : Repr GameState where
  reprPrec state n := reprPrec state.board n

open GameState Color NormalMove Move PieceType Castle

/-- Return the square with an offset of `(df, dr)` from square `sq` (`df` is along file, `dr` is along rank) -/
def Square.offsetSquare (sq : Square) (df dr : Int) : Option Square :=
  let f := sq.file.val + df
  let r := sq.rank.val + dr
  if h : 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 then
    some { file := ⟨f.toNat, by grind⟩, rank := ⟨r.toNat, by grind⟩ }
  else
    none

/-- Return all moves generated by offsets from square `startSq` -/
def GameState.generateStepMoves (state : GameState) (startSq : Square) (offsets : List (Int × Int))
    : List Move :=
  offsets.filterMap fun (df, dr) =>
    match startSq.offsetSquare df dr with
    | none => none
    | some targetSq =>
      match state.board targetSq with
      | some p => if p.color == state.turn then none else some <| normal ⟨startSq, targetSq⟩
      | none   => some <| normal ⟨startSq, targetSq⟩

/-- Return all valid slide moves in a direction -/
def Board.slideMove (board : Board) (color : Color) (startSq currentSq : Square) (df dr : Int) (fuel : Nat)
    : List Move :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match currentSq.offsetSquare df dr with
    | none => []
    | some nextSq =>
      match board nextSq with
      | none => -- empty; continue moving
        (normal ⟨startSq, nextSq⟩) :: (slideMove board color startSq nextSq df dr n)
      | some p =>
        if p.color != color then
          [normal ⟨startSq, nextSq⟩] -- Opponent piece; capture and stop
        else
          [] -- Own piece; stop before it

/-- Get a list of all possible slide moves in all given directions -/
def GameState.generateSlideMoves (state : GameState) (sq : Square) (directions : List (Int × Int))
    : List Move :=
  directions.flatMap fun (df, dr) => state.board.slideMove state.turn sq sq df dr 7

/-- Return all valid knight moves for knight at square `sq` -/
def GameState.knightMoves (state : GameState) (sq : Square) : List Move :=
  let offsets := [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]
  state.generateStepMoves sq offsets

/-- Return all valid rook moves for rook at square `sq` -/
def GameState.rookMoves (state : GameState) (sq : Square) : List Move :=
  let directions := [(0, 1), (0, -1), (1, 0), (-1, 0)]
  state.generateSlideMoves sq directions

/-- Return all valid bishop moves for bishop at square `sq` -/
def GameState.bishopMoves (state : GameState) (sq : Square) : List Move :=
  let directions := [(1, 1), (1, -1), (-1, 1), (-1, -1)]
  state.generateSlideMoves sq directions

/-- Return all valid queen moves for queen at square `sq` -/
def GameState.queenMoves (state : GameState) (sq : Square) : List Move :=
  let directions := [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)]
  state.generateSlideMoves sq directions

/-- Return all valid pawn moves for pawn at square `sq` -/
def GameState.pawnMoves (state : GameState) (sq : Square) : List Move :=
  singlePushMoves ++ doublePushMoves ++ captureMoves
  where
    dir := match state.turn with | .white => 1 | .black => -1
    singlePushMoves :=
      match sq.offsetSquare 0 dir with
      | none => [] -- not possible
      | some targetSq =>
        match state.board targetSq with
        | none => makePawnMovesAndPromotion sq targetSq
        | some _ => []
    startRank := match state.turn with | .white => 1 | .black => 6
    doublePushMoves :=
      if sq.rank == startRank then
        match sq.offsetSquare 0 dir, sq.offsetSquare 0 (2 * dir) with
        | some step1, some step2 =>
          match state.board step1, state.board step2 with
          | none, none => [normal ⟨sq, step2⟩]
          | _, _ => []
        | _, _ => [] -- not possible
      else []
    captureOffsets := [(-1, dir), (1, dir)]
    captureMoves := captureOffsets.flatMap fun (df, dr) =>
      match sq.offsetSquare df dr with
      | none => []
      | some targetSq =>
        -- Normal Capture
        let normalCap := match state.board targetSq with
          | some p => if p.color != state.turn then makePawnMovesAndPromotion sq targetSq else []
          | none => []
        -- En Passant Capture
        let epCap := match state.enPassantSq with
          | some epSq => if targetSq == epSq then [enPassant ⟨sq, targetSq⟩] else []
          | none => []
        normalCap ++ epCap
    makePawnMovesAndPromotion (fromSq toSq : Square) :=
      let isProm := match state.turn with
        | .white => toSq.rank == 7
        | .black => toSq.rank == 0
      if isProm then
        [ promotion ⟨fromSq, toSq, queen⟩,
          promotion ⟨fromSq, toSq, rook⟩,
          promotion ⟨fromSq, toSq, bishop⟩,
          promotion ⟨fromSq, toSq, knight⟩ ]
      else
        [ normal ⟨fromSq, toSq⟩ ]

def GameState.offsetPiece (state : GameState) (sq : Square) (df dr : Int)
    : Option Piece := do
  state.board <| ← sq.offsetSquare df dr

def GameState.hasCastlingRights (state : GameState) (col : Color) (side : Castle)
    : Bool :=
  match col, side with
  | white, kingside  => state.castling.whiteKingside
  | black, queenside => state.castling.blackQueenside
  | black, kingside  => state.castling.blackKingside
  | white, queenside => state.castling.whiteQueenside

/-- Return all valid king moves (does not check for checks) -/
def GameState.kingMoves (state : GameState) (sq : Square) : List Move :=
  normalMoves ++ kingsideMoves ++ queensideMoves
  where
    normalMoves := state.generateStepMoves sq
      [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)]
    kingsideMoves := if state.hasCastlingRights state.turn kingside then
        match state.offsetPiece sq 1 0, state.offsetPiece sq 2 0 with
        | none, none => [castle kingside]
        | _, _ => []
      else []
    queensideMoves := if state.hasCastlingRights state.turn queenside then
        match state.offsetPiece sq (-1) 0, state.offsetPiece sq (-2) 0 with
        | none, none => [castle queenside]
        | _, _ => []
      else []

/-- Return all valid moves for piece `p` at square `sq` in game -/
def GameState.generateMovesFor (state : GameState) (sq : Square) (p : Piece)
    : List Move :=
  if p.color != state.turn then []
  else match p.type with
    | pawn   => state.pawnMoves sq
    | knight => state.knightMoves sq
    | bishop => state.bishopMoves sq
    | rook   => state.rookMoves sq
    | queen  => state.queenMoves sq
    | king   => state.kingMoves sq

/-- List of all squares on chessboard -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f =>
    (List.finRange 8).map fun r =>
      { file := f, rank := r }

/-- Generate all pseudo-legal moves in game -/
def GameState.generateAllPseudoLegalMoves (state : GameState) : List Move :=
  allSquares.flatMap fun sq =>
    match state.board sq with
    | some p => state.generateMovesFor sq p
    | none   => []

/-- Update castling rights based on piece `p` moving from `fromSq` to `toSq` -/
def CastlingRights.update (rights : CastlingRights) (p : Piece) (fromSq toSq : Square)
    : CastlingRights :=
  match p.type, p.color with
  | .king, .white => { rights with whiteKingside := false, whiteQueenside := false}
  | .king, .black => { rights with blackKingside := false, blackQueenside := false }
  | _, _ => checkRook toSq <| checkRook fromSq rights
  where
  checkRook (sq : Square) (cr : CastlingRights) : CastlingRights :=
    if      sq.rank == 0 ∧ sq.file == 7 then { cr with whiteKingside := false }
    else if sq.rank == 0 ∧ sq.file == 0 then { cr with whiteQueenside := false }
    else if sq.rank == 7 ∧ sq.file == 7 then { cr with blackKingside := false }
    else if sq.rank == 7 ∧ sq.file == 0 then { cr with blackQueenside := false }
    else    cr

/-- Direction of pawn movement for color -/
def Color.getDir (col : Color) : Int :=
  match col with
  | white => 1
  | black => -1

/-- Move `piece` from `fromSq` to `toSq` on `board` -/
def Board.movePiece (board : Board) (piece : Piece) (fromSq toSq : Square)
    : Board :=
  board.update fromSq none |>.update toSq piece

/-- Apply a pseudo-legal move on a GameState -/
def GameState.applyPseudoLegalMove (state : GameState) (move : Move)
    : GameState :=
  match move with
  | normal m =>
    match state.board m.fromSq with
    | none => state
    | some piece =>
      { state with
        board := state.board.movePiece piece m.fromSq m.toSq
        turn := state.turn.opposite
        castling := state.castling.update piece m.fromSq m.toSq
        enPassantSq := getEnPassantState m piece
        captures := addCapture state m.toSq
        halfMoves := updateHalfMoves state piece m.toSq
        numMove := state.numMove + 1 }
  | castle m =>
    let rank : Rank := match state.turn with | white => 0 | black => 7
    let new_board := match m with
    | kingside => state.board.movePiece ⟨state.turn, king⟩ ⟨4,rank⟩ ⟨6,rank⟩
      |>.movePiece ⟨state.turn, rook⟩ ⟨7,rank⟩ ⟨5,rank⟩
    | queenside => state.board.movePiece ⟨state.turn, king⟩ ⟨4,rank⟩ ⟨2,rank⟩
      |>.movePiece ⟨state.turn, rook⟩ ⟨0,rank⟩ ⟨3,rank⟩
    { state with
      board := new_board
      turn := state.turn.opposite
      castling := state.castling.update ⟨state.turn, king⟩ ⟨4,rank⟩ ⟨6,rank⟩
      enPassantSq := none
      halfMoves := state.halfMoves + 1
      numMove := state.numMove + 1 }
  | promotion m =>
    let piece : Piece := ⟨state.turn, pawn⟩
    { state with
        board := state.board.movePiece piece m.fromSq m.toSq
          |>.update m.toSq (some ⟨state.turn, m.promotion⟩)
        turn := state.turn.opposite
        castling := state.castling.update piece m.fromSq m.toSq
        enPassantSq := none
        captures := addCapture state m.toSq
        halfMoves := 0
        numMove := state.numMove + 1 }
  | enPassant m =>
    let piece : Piece := ⟨state.turn, pawn⟩
    let captureSq : Square := match state.turn with
      | white => ⟨m.enPassantSq.file, 4⟩
      | black => ⟨m.enPassantSq.file, 3⟩
    { state with
        board := state.board.movePiece piece m.fromSq m.enPassantSq
          |>.update captureSq none
        turn := state.turn.opposite
        enPassantSq := none
        captures := addCapture state captureSq
        halfMoves := 0
        numMove := state.numMove + 1 }
  where
    getEnPassantState (m : NormalMove) (piece : Piece) :=
      match piece.type with
      | pawn =>
        let rankDiff := (m.toSq.rank : Int) - (m.fromSq.rank : Int)
        if rankDiff.natAbs == 2 then
          m.fromSq.offsetSquare 0 piece.color.getDir
        else none
      | _ => none
    addCapture (state : GameState) (toSq : Square) :=
      match state.board toSq with
      | none   => state.captures
      | some captured_piece =>
        match state.turn with
        | white => { state.captures with black := captured_piece :: state.captures.black }
        | black => { state.captures with white := captured_piece :: state.captures.white }
    updateHalfMoves (state : GameState) (p : Piece) (toSq : Square) :=
      match p.type with
      | pawn => 0
      | _ => match state.board toSq with
        | some _ => 0
        | none => state.halfMoves + 1

def findKing (b : Board) (c : Color) : Option Square :=
  allSquares.find? fun sq =>
    match b sq with
    | some p => p.color == c ∧ p.type == .king
    | none => false

/-- Returns a list of all attacked squares by all valid moves -/
def attackedSquares (state : GameState) : List Square :=
  let moves := generateAllPseudoLegalMoves state
  moves.foldl (
    fun lsq mv => match mv with
    | normal m => match state.board m.toSq with
      | some _ => m.toSq :: lsq
      | none   => lsq
    | promotion m => match state.board m.toSq with
      | some _ => m.toSq :: lsq
      | none   => lsq
    | enPassant m => m.enPassantSq :: lsq
    | castle _ => lsq
    )
  []

def IsInCheck (state : GameState) : Bool :=
  match findKing state.board state.turn with
  | none => False
  | some kingSq =>
    let flippedState := { state with turn := state.turn.opposite }
    kingSq ∈ attackedSquares flippedState

def IsPseudoLegalMove (state : GameState) (m : Move) : Bool :=
  m ∈ generateAllPseudoLegalMoves state

-- A move is strictly legal if it is pseudo-legal AND doesn't result in self-check.
def IsLegalMove (state : GameState) (m : Move) : Bool :=
  IsPseudoLegalMove state m ∧ ¬IsInCheck (applyPseudoLegalMove state m)

-- #synth Decidable IsLegalMove
-- set_option trace.Meta.synthInstance true

def GameState.playMove (state : GameState) (move : Move) : GameState :=
  if IsLegalMove state move then
    let state1 := state.applyPseudoLegalMove move
    { state1 with
      valid := true
      history := move :: state1.history
      messages := [] }
  else
    { state with
      valid := false
      messages := ["Illegal Move"] }

def GameState.play (state : GameState) (moves : List Move)
    : GameState :=
  moves.foldl (fun st mv => st.playMove mv) state

def game1 : GameState :=
  (default : GameState).play
    [
      n[5,2,5,3]
    ]

#eval game1
