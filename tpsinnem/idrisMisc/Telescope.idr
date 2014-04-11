module tpsinnem.idrisMisc.Telescope

import tpsinnem.idrisMisc.Pos
import Data.Vect

%default total

---------------------------------
--  Yet another telescope type?
--  - I aim this to essentially be a 'witness that a type is a depth-n
--    right-nested dependent pair type'.
--    - But:
--      - Does it actually do that?
--      - Is that sufficient for what people want from telescopes?
---------------------------------

data Tscope : Pos -> Type -> Type where

  tsBase :  (A:Type) -> Tscope one A

  tsCons :  {n:Pos} -> (A:Type) -> (P : A -> Type) ->
            ((a:A) -> Tscope n (P a)) -> Tscope (psuc n) (Exists A P)


data Telescope : Type where
  telescope : {n:Pos} -> {C:Type} -> Tscope n C -> Telescope

TsColl : {n:Pos} -> {C:Type} -> Tscope n C -> Type
TsColl {C} _ = C

TsCollapse : Telescope -> Type
TsCollapse (telescope ts) = TsColl ts

----------------------------------
--  Syntax
----------------------------------

syntax "#[" [type] "]#"
  = tsBase type

syntax "#[" {name} ":" [type] "]=" [tail]
  = tsCons type (\name => TsColl tail) (\name => tail)

-------------------------------
--  An experiment. Compare: https://gist.github.com/copumpkin/4197012
-------------------------------

sugary : Telescope
sugary = telescope ( #[l:Nat]= #[v : Vect l Nat]= #[Elem l v]# )

manual : Telescope
manual = telescope $  tsCons
                        Nat 
                        (\l => (v : Vect l Nat ** (Elem l v)))
                        (\l =>
                          tsCons
                            (Vect l Nat)
                            (\v => Elem l v)
                            (\v => 
                              tsBase (Elem l v)))

elv : TsCollapse sugary
elv = (4 ** ([10, 0, 42, 4] ** (There $ There $ There $ Here)))

--  Won't typecheck:
--  notElv : TsCollapse sugary
--  notElv = (4 ** ([10, 0, 42, 3] ** (There $ There $ There $ Here)))

---------------------
--  'Regular' telescope type, naïvely adapted from 'Cx' in
--  https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf
--  - Not entirely directly adapted, though. Differences:
--    - I deal with Type rather than a custom code for types.
--    - I have an arbitrary Type already in the base case.
---------------------

mutual

  data RegularTelescope : Type where

    rtsBase : Type -> RegularTelescope

    rtsCons : (tail:RegularTelescope) ->
              (head : TsSeq tail -> Type) -> RegularTelescope


  TsSeq : RegularTelescope -> Type
  TsSeq (rtsBase a)          = a
  TsSeq (rtsCons tail head)  = (tseq : TsSeq tail ** head tseq) 

