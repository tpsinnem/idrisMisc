module tpsinnem.idrisMisc.Telescope

import tpsinnem.idrisMisc.Pos
import Data.Vect

%default total

--------------------
--  STOP PRESS!: Might you produce worthless Tscopeys by stuffing tsConses with
--  somethings resembling FalseElim?
--------------------
||| Yet another telescope type?
||| * I aim this to essentially be a 'witness that a type is a depth-n 
|||   right-nested dependent pair type'.
|||     * But:
|||         * Does it actually do that?
|||         * Is that sufficient for what people want from telescopes?
|||
||| @ length Positive integer length.
||| @ C      Accumulation of a right-nested dependent pair type.
---------------------------------

data Tscopey : (length:Pos) -> (C:Type) -> Type where

  tsBase :  (A:Type) -> Tscopey one A

  tsCons :  {n:Pos} -> (A:Type) -> (P : A -> Type) ->
            ((a:A) -> Tscopey n (P a)) -> Tscopey (psuc n) (Exists A P)

||| This exists for the sake of tidier type declarations, if one wants such.
data Telescopey : Type where
  telescopey : {n:Pos} -> {C:Type} -> Tscopey n C -> Telescopey

||| 'Collapse' a Tscopey to the accumulated nested dependent pair type.
tsColl : {n:Pos} -> {C:Type} -> Tscopey n C -> Type
tsColl {C} _ = C

||| 'Collapse' a Telescopey to the accumulated nested dependent pair type.
tsCollapse : Telescopey -> Type
tsCollapse (telescopey ts) = tsColl ts


--------------------------------------------------
--  Syntax: #[a:Foo]= #[b : Bar a]= #[Quux a b]#
--------------------------------------------------

syntax "#[" [type] "]#"
  = tsBase type

syntax "#[" {name} ":" [type] "]=" [tail]
  = tsCons type (\name => tsColl tail) (\name => tail)


-------------------------------
--  An experiment. Adapted from https://gist.github.com/copumpkin/4197012
-------------------------------

sugary : Telescopey
sugary = telescopey ( #[l:Nat]= #[v : Vect l Nat]= #[Elem l v]# )

manual : Telescopey
manual = telescopey $ tsCons  Nat 
                              (\l => (v : Vect l Nat ** (Elem l v)))
                              (\l => tsCons (Vect l Nat)
                                            (\v => Elem l v)
                                            (\v => tsBase (Elem l v)))
elv : tsCollapse sugary
elv = (4 ** ([10, 0, 42, 4] ** (There $ There $ There $ Here)))

--  Won't typecheck:
--  notElv : tsCollapse sugary
--  notElv = (4 ** ([10, 0, 42, 3] ** (There $ There $ There $ Here)))


---------------------
--  'Regularish' telescope type, naïvely adapted from 'Cx' in
--  https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf
--  - A difference is that this one deals with Type rather than a custom code
--    for types.
---------------------

mutual

  data RegularishTscope: Type where

    rtsEmpty :  RegularishTscope

    rtsCons  :  (tail : RegularishTscope) ->
                (head : rtsColl tail -> Type) -> RegularishTscope

  rtsColl : RegularishTscope -> Type
  rtsColl rtsEmpty            = ()
  rtsColl (rtsCons tail head) = (ctail : rtsColl tail ** head ctail) 


-------------------------
--  A variant of the above regularish type, truncated in the sense that,
--  like in 'Tscopey', there is not first an 'empty' base case.
--  - Does that difference break anything?
-------------------------

mutual

  data RegularishTsTruncated : Type where

    rtstBase :  Type -> RegularishTsTruncated

    rtstCons :  (tail : RegularishTsTruncated) ->
                (head : rtstColl tail -> Type) -> RegularishTsTruncated

  rtstColl : RegularishTsTruncated -> Type
  rtstColl (rtstBase a)          = a
  rtstColl (rtstCons tail head)  = (ctail : rtstColl tail ** head ctail) 

