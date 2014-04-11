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

  tsBase :  (a:Type) -> Tscope one a

  tsCons :  {n:Pos} -> (a:Type) -> (p : a -> Type) ->
            ((a0:a) -> Tscope n (p a0)) -> Tscope (psuc n) (Exists a p)


data Telescope : Type where
  telescope : {n:Pos} -> {c:Type} -> Tscope n c -> Telescope


--  Should this be defined for Telescope instead?
tsCollapse : {n:Pos} -> {c:Type} -> Tscope n c -> Type
tsCollapse {c} _ = c

--  Well, have it both ways..
tsCollapse' : Telescope -> Type
tsCollapse' (telescope ts) = tsCollapse ts

----------------------------------
--  Syntax
--  - Alternative formulations very welcome!
----------------------------------

syntax "#[" [type] "]#"
  = tsBase type

syntax "#[" {name} ":" [type] "]=" [tail]
  = tsCons type (\name => tsCollapse tail) (\name => tail)

-------------------------------
--  An experiment. Compare: https://gist.github.com/copumpkin/4197012
-------------------------------

elv : Tscope (psuc $ psuc $ one) (l:Nat ** (v : Vect l Nat ** (Elem l v)))
elv = tsCons
        Nat 
        (\l => (v : Vect l Nat ** (Elem l v)))
        (\l =>
          tsCons
            (Vect l Nat)
            (\v => Elem l v)
            (\v => 
              tsBase (Elem l v)))

elv2 : Telescope
elv2 = telescope ( #[l:Nat]= #[v : Vect l Nat]= #[Elem l v]# )

anElv : tsCollapse' elv2
anElv = (4 ** ([10, 0, 42, 4] ** (There $ There $ There $ Here)))

--  Won't typecheck:
--  notAnElv : tsCollapse' elv2
--  notAnElv = (4 ** ([10, 0, 42, 3] ** (There $ There $ There $ Here)))

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

