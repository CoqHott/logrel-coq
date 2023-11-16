sort : Type
term(tRel) : Type

set : sort
formula : sort
irr : term -> sort

tSort : sort -> term

tProd : term -> (bind term in term) -> term
tLambda : term -> (bind term in term) -> term
tApp : term -> term -> term

tNat : term
tZero : term
tSucc : term -> term
tNatElim : (bind term in term) -> term -> term -> term -> term

tEmpty : term
tEmptyElim : (bind term in term) -> term -> term

tSig : term -> (bind term in term) -> term
tPair : term -> (bind term in term) -> term -> term -> term
tFst : term -> term
tSnd : term -> term

tId : term -> term -> term -> term
tRefl : term -> term -> term
tIdElim : term -> term -> (bind term , term in term) -> term -> term -> term -> term