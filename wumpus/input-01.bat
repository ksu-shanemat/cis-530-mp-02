(reset)
(assert (smell   1 1 false))
(assert (breeze  1 1 false))
(assert (glitter 1 1 false))
(assert (wumpus  1 1 false))
(assert (pit     1 1 false))
(assert (gold    1 1 false))

(assert (smell   1 2 true))
(assert (breeze  1 2 false))
(assert (glitter 1 2 false))
(assert (wumpus  1 2 false))
(assert (pit     1 2 false))
(assert (gold    1 2 false))

(assert (smell   2 1 false))
(assert (breeze  2 1 true))
(assert (glitter 2 1 false))
(assert (wumpus  2 1 false))
(assert (pit     2 1 false))
(assert (gold    2 1 false))

(run)

(facts)