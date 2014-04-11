module tpsinnem.idrisMisc.Telescope

import tpsinnem.idrisMisc.Pos
import Data.Vect

%default total

---------------------------------
--  Yet another telescope type?
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

tsCollapse' : Telescope -> Type
tsCollapse' (telescope ts) = tsCollapse ts

----------------------------------
--  Syntax
----------------------------------

syntax "-##" "[" [type] "]" "#"
  = tsBase type

syntax "-##" "[" {name} ":" [type] "]" "-=" [tail] "#"
  = tsCons type (\name => tsCollapse tail) (\name => tail)

-------------------------------
--  An experiment. Compare: https://gist.github.com/copumpkin/4197012
-------------------------------

elv : Tscope (psuc $ psuc $ one) (l:Nat ** (v : Vect l Nat ** (Elem l v)))
elv = tsCons
        Nat 
        (\l => (v : Vect l Nat ** (Elem l v))) -- NOTE -- SYNTAX
        (\l =>
          tsCons
            (Vect l Nat)
            (\v => Elem l v)
            (\v => 
              tsBase (Elem l v)))

elv2 : Telescope
elv2 = telescope (-## [l:Nat] -= (-## [v : Vect l Nat] -= (-## [Elem l v] #) #) #)

---------------------
--  'Regular' telescope type, naïvely adapted from
--  https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf
---------------------

mutual

  data RegularTelescope : Type where

    rtsBase : Type -> RegularTelescope

    rtsCons : (tail:RegularTelescope) ->
              (head : TsSeq tail -> Type) -> RegularTelescope


  TsSeq : RegularTelescope -> Type
  TsSeq (rtsBase a)          = a
  TsSeq (rtsCons tail head)  = (tseq : TsSeq tail ** head tseq) 

---------------------------------
--  Syntax thoughts:
---------------------------------

--  I think this one is the winner:

  -- elv = -## [l:Nat] -= (-## [v : Vect l nat] -= (-## [Elem l v] #) #) #

--  Runner-up:

  -- elv = -## [l:Nat] -= (-## [v : Vect l nat] -= (-## [Elem l v] ##-) ##-) ##-

--  Other candidates:

  -- elv = #> (l:Nat) =- (#> (v : Vect l nat) =- (#> (Elem l v) <#) <#) <#

  -- elv = #> (l:Nat) ==- (#> (v : Vect l nat) ==- (#> (Elem l v) <#) <#) <#

  -- elv = #>(l:Nat) =- (#>(v : Vect l nat) =- (#>(Elem l v)<#)<#)<#

  -- elv = #- (l:Nat) =- (#- (v : Vect l nat) =- (#- (Elem l v) -#) -#) -#

  -- elv = #< (l:Nat) =- (#< (v : Vect l nat) =- (#< (Elem l v) >#) >#) >#

  -- elv = ##- (l:Nat) =- (##- (v : Vect l nat) =- (##- (Elem l v) -##) -##) -##

  -- elv = -## (l:Nat) =- (-## (v : Vect l nat) =- (-## (Elem l v) ##-) ##-) ##-

  -- elv = -# (l:Nat) =- (-# (v : Vect l nat) =- (-# (Elem l v) #-) #-) #-

  -- elv = -## (l:Nat) =- (-## (v : Vect l nat) =- (-## (Elem l v) ##-) ##-) ##-

  -- elv = -## (l:Nat) -= (-## (v : Vect l nat) -= (-## (Elem l v) ##-) ##-) ##-

  -- elv = -## [[l:Nat]] -= (-## [[v : Vect l nat]] -= (-## [[Elem l v]] ##-) ##-) ##-

  -- elv = -# [[l:Nat]] -= (-# [[v : Vect l nat]] -= (-# [[Elem l v]] #-) #-) #-

  -- elv = -# [l:Nat] -= (-# [v : Vect l nat] -= (-# [Elem l v] #-) #-) #-

-----------------------
--  Notes
-----------------------

--  SYNTAX
--  - (\l => tsCollapse ((\l => [{yet undesugared expression here?}]) l)).
--    - But would that be reasonable?
--      - Recursion restrictions on syntax rules might prevent anything that
--        isn't a little bonkers.

