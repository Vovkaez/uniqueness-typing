# Uniqueness typing
An implementation of type reconstruction for simply typed lambda calculus extended with uniqueness types, as described in Edsko de Vries, Rinus Plasmeijer, David M Abrahamson. Uniqueness Typing Simplified.
# How to run
CLI can be run via `stack run`. Single lambda term is expected on one line. You can exit by typing `q` or `quit`.
# Example
```
vova@main-vm:~/uniqueness-typing$ stack run
\x. x
(t0{u0}) -0> (t0{u0})
\x.\y.x
(t0{u0}) -0> ((t1{u1}) -u0> (t0{u0}))
\f.\x.(f x) x
((t1{0}) -u3> ((t1{0}) -u5> (t3{u4}))) -0> ((t1{0}) -u3> (t3{u4}))
\p. p (\x.\y.x)
(((t1{u1}) -u4> ((t2{u2}) -(u1) ∨ (u4)> (t1{u1}))) -u4> (t3{u3})) -0> (t3{u3})
quit
Exiting
vova@main-vm:~/uniqueness-typing$
```