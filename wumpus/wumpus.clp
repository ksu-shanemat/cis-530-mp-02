(deftemplate sq "Represents information about given square"
	(slot x); Column number
	(slot y); Row number
	(slot s); Smelly indicator
	(slot b); Breeze indicator
	(slot g); Glitter indicator
	(slot w); Wumpus indicator
	(slot p); Pit indicator
	(slot t); Treasure indicator
)

(defglobal
	?*xMin* = 1
	?*xMax* = 4
	?*yMin* = 1
	?*yMax* = 4
)

(deffacts gridInit "Initialization of grid squares"
	(sq (x 1) (y 1) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 1) (y 2) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 1) (y 3) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 1) (y 4) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 2) (y 1) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 2) (y 2) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 2) (y 3) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 2) (y 4) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 3) (y 1) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 3) (y 2) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 3) (y 3) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 3) (y 4) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 4) (y 1) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 4) (y 2) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 4) (y 3) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
	(sq (x 4) (y 4) (s nil) (b nil) (g nil) (w nil) (p nil) (t nil))
)

(defrule set-s "Sets the smell flag to square"
	(smell ?column ?row ?value)
	?prev <- (sq (x ?x&:(eq ?x ?column)) (y ?y&:(eq ?y ?row)) (s nil) (b ?b) (g ?g) (w ?w) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?x) (y ?y) (s ?value) (b ?b) (g ?g) (w ?w) (p ?p) (t ?t)))
)

(defrule set-b "Sets the breeze flag to square"
	(breeze ?column ?row ?value)
	?prev <- (sq (x ?x&:(eq ?x ?column)) (y ?y&:(eq ?y ?row)) (s ?s) (b nil) (g ?g) (w ?w) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?x) (y ?y) (s ?s) (b ?value) (g ?g) (w ?w) (p ?p) (t ?t)))
)

(defrule set-g "Sets the glitter flag to square"
	(glitter ?column ?row ?value)
	?prev <- (sq (x ?x&:(eq ?x ?column)) (y ?y&:(eq ?y ?row)) (s ?s) (b ?b) (g nil) (w ?w) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?x) (y ?y) (s ?s) (b ?b) (g ?value) (w ?w) (p ?p) (t ?t)))
)

(defrule set-w "Sets the wumpus flag to square"
	(wumpus ?column ?row ?value)
	?prev <- (sq (x ?x&:(eq ?x ?column)) (y ?y&:(eq ?y ?row)) (s ?s) (b ?b) (g ?g) (w nil) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?x) (y ?y) (s ?s) (b ?b) (g ?g) (w ?value) (p ?p) (t ?t)))
)

(defrule set-p "Sets the pit flag to square"
	(pit ?column ?row ?value)
	?prev <- (sq (x ?x&:(eq ?x ?column)) (y ?y&:(eq ?y ?row)) (s ?s) (b ?b) (g ?g) (w ?w) (p nil) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?x) (y ?y) (s ?s) (b ?b) (g ?g) (w ?w) (p ?value) (t ?t)))
)

(defrule set-t "Sets the treasure flag to square"
	(treasure ?column ?row ?value)
	?prev <- (sq (x ?x&:(eq ?x ?column)) (y ?y&:(eq ?y ?row)) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?x) (y ?y) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t ?value)))
)

(defrule wumpus-left "Inference for wumpus to the left from smelly square"
	; Center square
	(sq (x ?x) (y ?y) (s true) (b ?) (g ?) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Left square
	?prev <- (sq (x ?lx&:(eq ?lx (- ?x 1))) (y ?ly&:(eq ?ly ?y)) (s ?ls) (b ?lb) (g ?lg) (w nil) (p ?lp) (t ?lt))
	=>
	(retract ?prev)
	(assert (sq (x ?lx) (y ?ly) (s ?ls) (b ?lb) (g ?lg) (w true) (p ?lp) (t ?lt)))
)

(defrule no-wumpus-left "Propagates the information that there is not wumpus on the left, if there is no smell on the square"
	(sq (x ?x) (y ?y) (s false) (b ?) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?lx&:(eq ?lx (- ?x 1))) (y ?ly&:(eq ?ly ?y)) (s ?s) (b ?b) (g ?g) (w nil) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?lx) (y ?ly) (s ?s) (b ?b) (g ?g) (w false) (p ?p) (t ?t)))
)

(defrule wumpus-right "Inference for wumpus to the right from smelly square"
	; Center square
	(sq (x ?x) (y ?y) (s true) (b ?) (g ?) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Right square
	?prev <- (sq (x ?rx&:(eq ?rx (+ ?x 1))) (y ?ry&:(eq ?ry ?y)) (s ?rs) (b ?rb) (g ?rg) (w nil) (p ?rp) (t ?rt))
	=>
	(retract ?prev)
	(assert (sq (x ?rx) (y ?ry) (s ?rs) (b ?rb) (g ?rg) (w true) (p ?rp) (t ?rt)))
)

(defrule no-wumpus-right "Propagates the information that there is not wumpus on the right, if there is no smell on the square"
	(sq (x ?x) (y ?y) (s false) (b ?) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?rx&:(eq ?rx (+ ?x 1))) (y ?ry&:(eq ?ry ?y)) (s ?s) (b ?b) (g ?g) (w nil) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?rx) (y ?ry) (s ?s) (b ?b) (g ?g) (w false) (p ?p) (t ?t)))
)

(defrule wumpus-top "Inference for wumpus above smelly square"
	; Center square
	(sq (x ?x) (y ?y) (s true) (b ?) (g ?) (w ?) (p ?) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Top square
	?prev <- (sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(eq ?ty (+ ?y 1))) (s ?ts) (b ?tb) (g ?tg) (w nil) (p ?tp) (t ?tt))
	=>
	(retract ?prev)
	(assert (sq (x ?tx) (y ?ty) (s ?ts) (b ?tb) (g ?tg) (w true) (p ?tp) (t ?tt)))
)

(defrule no-wumpus-top "Propagates the information that there is not wumpus above, if there is no smell on the square"
	(sq (x ?x) (y ?y) (s false) (b ?) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(eq ?ty (+ ?y 1))) (s ?s) (b ?b) (g ?g) (w nil) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?tx) (y ?ty) (s ?s) (b ?b) (g ?g) (w false) (p ?p) (t ?t)))
)

(defrule wumpus-bot "Inference for wumpus bellow smelly square"
	; Center square
	(sq (x ?x) (y ?y) (s true) (b ?) (g ?) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w false) (p ?) (t ?))
	; Bottom square
	?prev <- (sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(eq ?by (- ?y 1))) (s ?bs) (b ?bb) (g ?bg) (w nil) (p ?bp) (t ?bt))
	=>
	(retract ?prev)
	(assert (sq (x ?bx) (y ?by) (s ?bs) (b ?bb) (g ?bg) (w true) (p ?bp) (t ?bt)))
)

(defrule no-wumpus-bot "Propagates the information that there is not wumpus bellow, if there is no smell on the square"
	(sq (x ?x) (y ?y) (s false) (b ?) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(eq ?by (- ?y 1))) (s ?s) (b ?b) (g ?g) (w nil) (p ?p) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?bx) (y ?by) (s ?s) (b ?b) (g ?g) (w false) (p ?p) (t ?t)))
)

(defrule pit-left "Inference for pit to the left from breezy square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b true) (g ?) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Left square
	?prev <- (sq (x ?lx&:(eq ?lx (- ?x 1))) (y ?ly&:(eq ?ly ?y)) (s ?ls) (b ?lb) (g ?lg) (w ?lw) (p nil) (t ?lt))
	=>
	(retract ?prev)
	(assert (sq (x ?lx) (y ?ly) (s ?ls) (b ?lb) (g ?lg) (w ?lw) (p true) (t ?lt)))
)

(defrule no-pit-left "Propagates the information that there is not pit on the left, if there is no breeze on the square"
	(sq (x ?x) (y ?y) (s ?) (b false) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?lx&:(eq ?lx (- ?x 1))) (y ?ly&:(eq ?ly ?y)) (s ?s) (b ?b) (g ?g) (w ?w) (p nil) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?lx) (y ?ly) (s ?s) (b ?b) (g ?g) (w ?w) (p false) (t ?t)))
)

(defrule pit-right "Inference for pit to the right from breezy square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b true) (g ?) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Right square
	?prev <- (sq (x ?rx&:(eq ?rx (+ ?x 1))) (y ?ry&:(eq ?ry ?y)) (s ?rs) (b ?rb) (g ?rg) (w ?rw) (p nil) (t ?rt))
	=>
	(retract ?prev)
	(assert (sq (x ?rx) (y ?ry) (s ?rs) (b ?rb) (g ?rg) (w ?rw) (p true) (t ?rt)))
)

(defrule no-pit-right "Propagates the information that there is not pit on the right, if there is no breeze on the square"
	(sq (x ?x) (y ?y) (s ?) (b false) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?rx&:(eq ?rx (+ ?x 1))) (y ?ry&:(eq ?ry ?y)) (s ?s) (b ?b) (g ?g) (w ?w) (p nil) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?rx) (y ?ry) (s ?s) (b ?b) (g ?g) (w ?w) (p false) (t ?t)))
)

(defrule pit-top "Inference for pit above breezy square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b true) (g ?) (w ?) (p ?) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Top square
	?prev <- (sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(eq ?ty (+ ?y 1))) (s ?ts) (b ?tb) (g ?tg) (w ?tw) (p nil) (t ?tt))
	=>
	(retract ?prev)
	(assert (sq (x ?tx) (y ?ty) (s ?ts) (b ?tb) (g ?tg) (w ?tw) (p true) (t ?tt)))
)

(defrule no-pit-top "Propagates the information that there is not pit above, if there is no breeze on the square"
	(sq (x ?x) (y ?y) (s ?) (b false) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(eq ?ty (+ ?y 1))) (s ?s) (b ?b) (g ?g) (w ?w) (p nil) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?tx) (y ?ty) (s ?s) (b ?b) (g ?g) (w ?w) (p false) (t ?t)))
)

(defrule pit-bot "Inference for pit bellow breezy square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b true) (g ?) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w ?) (p false) (t ?))
	; Bottom square
	?prev <- (sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(eq ?by (- ?y 1))) (s ?bs) (b ?bb) (g ?bg) (w ?bw) (p nil) (t ?bt))
	=>
	(retract ?prev)
	(assert (sq (x ?bx) (y ?by) (s ?bs) (b ?bb) (g ?bg) (w ?bw) (p true) (t ?bt)))
)

(defrule no-pit-bot "Propagates the information that there is not pit bellow, if there is no breeze on the square"
	(sq (x ?x) (y ?y) (s ?) (b false) (g ?) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(eq ?by (- ?y 1))) (s ?s) (b ?b) (g ?g) (w ?w) (p nil) (t ?t))
	=>
	(retract ?prev)
	(assert (sq (x ?bx) (y ?by) (s ?s) (b ?b) (g ?g) (w ?w) (p false) (t ?t)))
)

(defrule treasure-left "Inference for treasure to the left from glittering square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b ?) (g true) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Left square
	?prev <- (sq (x ?lx&:(eq ?lx (- ?x 1))) (y ?ly&:(eq ?ly ?y)) (s ?ls) (b ?lb) (g ?lg) (w ?lw) (p ?lp) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?lx) (y ?ly) (s ?ls) (b ?lb) (g ?lg) (w ?lw) (p ?lp) (t true)))
)

(defrule no-treasure-left "Propagates the information that there is not treasure on the left, if there is no glitter on the square"
	(sq (x ?x) (y ?y) (s ?) (b ?) (g false) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?lx&:(eq ?lx (- ?x 1))) (y ?ly&:(eq ?ly ?y)) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?lx) (y ?ly) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t false)))
)

(defrule treasure-right "Inference for treasure to the right from glittering square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b ?) (g true) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Right square
	?prev <- (sq (x ?rx&:(eq ?rx (+ ?x 1))) (y ?ry&:(eq ?ry ?y)) (s ?rs) (b ?rb) (g ?rg) (w ?rw) (p ?rp) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?rx) (y ?ry) (s ?rs) (b ?rb) (g ?rg) (w ?rw) (p ?rp) (t true)))
)

(defrule no-treasure-right "Propagates the information that there is not treasure on the right, if there is no glitter on the square"
	(sq (x ?x) (y ?y) (s ?) (b ?) (g false) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?rx&:(eq ?rx (+ ?x 1))) (y ?ry&:(eq ?ry ?y)) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?rx) (y ?ry) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t false)))
)

(defrule treasure-top "Inference for treasure above glittering square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b ?) (g true) (w ?) (p ?) (t ?))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Bottom square
	(sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(or (eq ?y ?*yMin*) (eq ?by (- ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Top square
	?prev <- (sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(eq ?ty (+ ?y 1))) (s ?ts) (b ?tb) (g ?tg) (w ?tw) (p ?tp) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?tx) (y ?ty) (s ?ts) (b ?tb) (g ?tg) (w ?tw) (p ?tp) (t true)))
)

(defrule no-treasure-top "Propagates the information that there is not treasure above, if there is no glitter on the square"
	(sq (x ?x) (y ?y) (s ?) (b ?) (g false) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(eq ?ty (+ ?y 1))) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?tx) (y ?ty) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t false)))
)

(defrule treasure-bot "Inference for treasure bellow glittering square"
	; Center square
	(sq (x ?x) (y ?y) (s ?) (b ?) (g true) (w ?) (p ?) (t ?))
	; Top square
	(sq (x ?tx&:(eq ?tx ?x)) (y ?ty&:(or (eq ?y ?*yMax*) (eq ?ty (+ ?y 1)))) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Left square
	(sq (x ?lx&:(or (eq ?x ?*xMin*) (eq ?lx (- ?x 1)))) (y ?ly&:(eq ?ly ?y)) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Right square
	(sq (x ?rx&:(or (eq ?x ?*xMax*) (eq ?rx (+ ?x 1)))) (y ?ry&:(eq ?ry ?y)) (s ?) (b ?) (g ?) (w ?) (p ?) (t false))
	; Bottom square
	?prev <- (sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(eq ?by (- ?y 1))) (s ?bs) (b ?bb) (g ?bg) (w ?bw) (p ?bp) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?bx) (y ?by) (s ?bs) (b ?bb) (g ?bg) (w ?bw) (p ?bp) (t true)))
)

(defrule no-treasure-bot "Propagates the information that there is not treasure bellow, if there is no glitter on the square"
	(sq (x ?x) (y ?y) (s ?) (b ?) (g false) (w ?) (p ?) (t ?))
	?prev <- (sq (x ?bx&:(eq ?bx ?x)) (y ?by&:(eq ?by (- ?y 1))) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t nil))
	=>
	(retract ?prev)
	(assert (sq (x ?bx) (y ?by) (s ?s) (b ?b) (g ?g) (w ?w) (p ?p) (t false)))
)
