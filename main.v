Require Import Setoid.


Record GroupTheo : Type := groupTheo
  { Gt : Set; (* nosnik *)
    opt : Gt -> Gt -> Gt; (* operacja *)
    assoct : forall(x y z : Gt), opt (opt x y) z = opt x (opt y z);
    neutt := forall(x : Gt), exists( e : Gt), opt e x = x /\ opt x e = x;
    invt := forall(x : Gt), exists( e y : Gt) , opt x y = e /\ opt y x  = e; 
  }.

(* Jednoznaczność elementu neutralnego *)
Definition idPro (g : GroupTheo ) (e : Gt g) := (forall(x : Gt g), opt g e x = x /\ opt g x e = x).

Theorem exOnlyOne : forall (g : GroupTheo), forall( e f : Gt g), (idPro g e /\ idPro g f) -> e = f.
Proof.  
  unfold idPro.
  intros.
  destruct H.
  pose proof H f as F.
  pose proof H0 e as E.
  destruct E.
  destruct F.
  rewrite <- H2.
  trivial.
Qed.

(* Jednoznaczność odwrotności  *)
Definition invPro (g : GroupTheo) (e y : Gt g):= idPro g e /\ ( forall(x : Gt g) ,( opt g x y = e /\ opt g y x  = e)).

Theorem exOnlyOneInv : forall( g : GroupTheo), forall (e y1 y2 x : Gt g), invPro g e y1 /\ invPro g e y2 -> y1 = y2.
Proof.
  unfold invPro.
  unfold idPro.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  pose proof H y1.
  destruct H3.
  pose proof H y2.
  destruct H5.
  rewrite <- H4.
  rewrite <- H5.
  pose proof H1 x.
  pose proof H2 x.
  destruct H7.
  destruct H8.
  rewrite <- H8 at 1.
  rewrite <- H9 at 1.
  rewrite (assoct ).
  trivial.
Qed.

(* Definicja grupy z uwzględnieniem jednoznaczności elementu e oraz jednoznaczności odwrotności *)
Record Group : Type := group
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    inv : G -> G;
    e : G;
  
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    id :  forall(x : G), op e x = e /\ op x e = e ;
    inverse :  forall(x : G), op x (inv x) = e /\ op (inv x) x  = e ;
  }.
