module tpsinnem.idrisMisc.Logic

%default total

data If : Type -> Type -> Type where
  yesThus :     a           -> b          ->  If a b
  not     :     (a -> _|_)  ->                If a b

data IfNot : Type -> Type -> Type where
  notThus :     (a -> _|_)  -> b          ->  IfNot a b
  yes     :     a           ->                IfNot a b

data NotIf : Type -> Type -> Type where
  yesThusNot :  a           -> (b -> _|_) ->  NotIf a b
  indeedNot  :  (a -> _|_)  ->                NotIf a b

data NotIfNot : Type -> Type -> Type where
  notThusNot :  (a -> _|_)  -> (b -> _|_) ->  NotIfNot a b
  indeedYes  :  a           ->                NotIfNot a b
