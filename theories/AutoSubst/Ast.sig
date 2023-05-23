sort : Type
term(tRel) : Type

option : Functor 

tSort : sort -> term

tProd : term -> (bind term in term) -> term
tLambda : "option" (term) -> (bind term in term) -> term
tApp : term -> term -> term

tNat : term
tZero : term
tSucc : term -> term
tNatElim : (bind term in term) -> term -> term -> term -> term

tEmpty : term
tEmptyElim : (bind term in term) -> term -> term

tSig : term -> (bind term in term) -> term
tPair : (bind term in "option" (term)) -> term -> term -> term
tFst : term -> term
tSnd : term -> term