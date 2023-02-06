Notes on the development.


# Porting from Agda to Coq

## Mutual induction

## Universe levels

Agda uses a type of universe levels that have to be explicited. It allows in
particular algebraic universe expressions that are not available in Coq. In
order to port the code to Coq, we have to replace the occurences of algebraic
universe expressions by fresh universe variables with corresponding constraints.

## Notations

## Adding automation (gen_typing)


# Novelties of this development

## Common interface to bidirectional and declarative typing

## Ltac derivation of well-formedness conditions of judgments
