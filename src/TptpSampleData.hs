module TptpSampleData where

problems = [
  ("simple",simple),
  ("eqAxiom",eqAxiom),
  ("barber",barber),
  ("pelletier20",pelletier20),
  ("pelletier24",pelletier24)]

simple = "fof(simple, conjecture, (?[X]:(![Y]: (p(X) => p(Y)))))."

eqAxiom = "fof(eqAxiom, conjecture, ((a1=a2) & (b1=b2) & (c1=c2)) => (f(a1,b1,c1)=f(a2,b2,c2)))."

barber = "fof(simple, conjecture, ~(?[B]:(![X]:(shaves(B,X) <=> ~shaves(X,X)))))."

pelletier20 = "\
\ fof(a1, axiom, (![X]: (![Y]: (?[Z]: (![W]: ((p(X) & q(Y)) => (r(Z) & u(W)))))))).\
\ fof(c, conjecture, (?[X]: (?[Y]: ((p(X) & q(Y)) => (?[Z]: r(Z))))))."

pelletier24 = "\
\ fof(a1, axiom, ~(?[X] : (u(X) & q(X)))).\
\ fof(a2, axiom, (![X] : (p(X) => (q(X) | r(X))))).\
\ fof(a3, axiom, ~(?[X] : (p(X) => (?[X]: q(X))))).\
\ fof(a4, axiom, (![X] : ((q(X) & r(X)) => u(X)))).\
\ fof(c, conjecture, (?[X] : (p(X) & r(X))))."
