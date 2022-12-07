sort : Type
aname : Type
term : Type

tSort : sort -> term
tProd : aname -> term -> (bind term in term) -> term
tLambda : aname -> term -> (bind term in term) -> term
tApp : term -> term -> term