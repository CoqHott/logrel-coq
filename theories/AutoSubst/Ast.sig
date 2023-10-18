sort : Type
term(tRel) : Type

typeLF : Type
termLF : Type

ctxLF : Type
subLF : Type

lfArr : typeLF -> typeLF -> typeLF

lfLam : typeLF -> termLF -> termLF
lfApp : termLF -> termLF -> termLF
lfSplice : term -> subLF -> termLF

lfCtxEmpty : ctxLF
lfCtxCons : ctxLF -> typeLF -> ctxLF

lfSubEmpty : subLF
lfWk : ctxLF -> subLF
lfSubCons : subLF -> termLF -> subLF

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

tCtx : term
tBox : ctxLF -> typeLF -> term
tQuote : ctxLF -> termLF -> term
tBoxRec : (bind term, term in term) -> term -> term -> term -> ctxLF -> term -> term