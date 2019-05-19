module TptpSampleData where

problems = [
  ("trivial",trivial),
  ("simple",simple),
  ("eqAxiom1",eqAxiom1),
  ("eqAxiom2",eqAxiom2),
  ("eqAxiom3",eqAxiom3),
  ("eqAxiom4",eqAxiom4),
  ("barber",barber),
  ("pelletier20",pelletier20),
  ("pelletier24",pelletier24)]

trivial = "fof(trivial, conjecture, ($true))."
simple = "fof(simple, conjecture, (?[X]:(![Y]: (p(X) => p(Y)))))."

eqAxiom1 = "fof(eqAxiom1, conjecture, ((a1=a2) & (b1=b2) & (c1=c2)) => (f(a1,b1,c1)=f(a2,b2,c2)))."
eqAxiom2 = "fof(eqAxiom2, conjecture, (a1=a2) => (f(a1,b1,c1)=f(a2,b1,c1)))."
eqAxiom3 = "fof(eqAxiom3, conjecture, ((a=b) & (b=c) & (c=d)) => (a=d))."
eqAxiom4 = "fof(eqAxiom4, conjecture, ((a=b)  => (b=a)))."

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
