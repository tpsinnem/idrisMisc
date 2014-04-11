module tpsinnem.idrisMisc.Pos

%default total

---------------
--  Positive integers
---------------

data Pos : Type where
  plusOne : Nat -> Pos

one : Pos
one = plusOne Z

psuc : Pos -> Pos
psuc (plusOne n) = plusOne (S n)


--  Part of me wants basic number types to be based on this instead:
--
--  data Pos : Type where
--    one : Pos
--    suc : Pos -> Pos

