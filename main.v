
Require Import Setoid. 


(* Typ grupy teoretycznej - zgodnie z definicją grupy z Bagińskiego *)
Record GroupTheo : Type := groupTheo
  { Gt : Set; (* nosnik *)
    opt : Gt -> Gt -> Gt; (* operacja *)
    assoct : forall(x y z : Gt), opt (opt x y) z = opt x (opt y z);
    neutt := exists( e : Gt), forall(x : Gt), opt e x = x /\ opt x e = x;
    invt := forall(e : Gt), (forall(x : Gt), opt e x = x /\ opt x e = x )->  forall(x : Gt), exists( y : Gt) , opt x y = e /\ opt y x  = e; 
  }.

(* Jednoznaczność elementu neutralnego - krótszy zapis*)
Definition idPro (g : GroupTheo ) (e : Gt g) := (forall(x : Gt g), opt g e x = x /\ opt g x e = x).

(* Twierdzenie, że istnieje dokładnie jeden element neutralny *)
Theorem exOnlyOneE : forall (g : GroupTheo), forall( e f : Gt g), (idPro g e /\ idPro g f) -> e = f.
Proof.  
  unfold idPro.
  intros.
  destruct H.
  specialize H with (x := f) .
  specialize H0 with (x := e) .
  destruct H, H0.
  rewrite <- H0.
  trivial.
Qed.


(* Jednoznaczność odwrotności - krótszy zapis  *)
Definition invPro (g : GroupTheo) (e y x : Gt g):= (  opt g x y = e /\ opt g y x  = e).

(* Twierdzenie, że dla dowolnego elementu istnieje jeden element odwrotny*)
Theorem exOnlyOneInv : forall( g : GroupTheo), forall (e x y1 y2 : Gt g), idPro g e /\ invPro g e y1 x /\  invPro g e y2 x -> y1 = y2.
(* Pomysł dowodu :*)
(* y1 =  y1 <*> e = y1 <*> (x <*> y2) = (y1 <*> x) <*> y2 = e <*> y2 = y2) *)
Proof.
  unfold invPro.
  unfold idPro.
  intros.
  destruct H.
  destruct H0.
  destruct H0, H1.
  specialize H with (x := y1) as Ey1 .
  specialize H with (x := y2) as Ey2 .
  destruct Ey1, Ey2.
  rewrite <- H5.
  rewrite <- H1.
  rewrite <- (assoct g).
  rewrite H2.
  trivial.
Qed.

(* Definicja grupy z uwzględnieniem jednoznaczności elementu neutralnego oraz jednoznaczności odwrotności *)
Record Group : Type := group
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    inv : G -> G;
    e : G;
  
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    id :  forall(x : G), op e x = x /\ op x e = x ;
    inverse :  forall(x : G), op x (inv x) = e /\ op (inv x) x  = e ;
  }.

Notation " x <* g *> y" := (op g x y) (at level 50).


Inductive In (g: Group) : Type := inSet (a : G g) | notInSet (b : G g).

Record SubGroup := subGroup
{
  Gr : Group;
  isInH : G Gr -> In Gr; 
  notEmpty : exists(x : G Gr), isInH x = inSet Gr x;
  cInv : forall(x : G Gr), isInH x = inSet Gr x -> isInH (inv Gr x) = inSet Gr (inv Gr x) ;
  cOp : forall(x y : G Gr), isInH x = inSet Gr x  /\  isInH y = inSet Gr y -> isInH (x <* Gr *> y) = inSet Gr (x <* Gr *> y) ;
}.

  


(* Definicja grupy abelowej *)
Record AbelianGroup : Type := aGroup 
  {
    abelGr : Group;
    comm : forall (x y : G abelGr), x <* abelGr *> y = y <* abelGr *> x;
  }.


(*lematy dające zachowanie równości przy mnożeniu przez ten sam element*)

Lemma lmult_a: forall (g : Group), forall (a b c : G g), b = c -> a <* g *> b = a <* g *> c.
Proof.
  intros. 
  rewrite H. 
  auto.
Qed.

Lemma rmult_a: forall (g : Group), forall (a b c : G g), b = c -> b <* g *> a = c <* g *> a.
Proof.
  intros. 
  rewrite H. 
  auto.
Qed.


(*Prawo skracania z lewej strony*)
Theorem cancelL: forall (g : Group), forall (a b c : G g), a <* g *> b = a <* g *> c -> b = c.
Proof.
  intros.
  pose (inv_prop := inverse g). (*wprowadzamy do założeń id g, assoc g i inv g*)
  pose (id_prop := id g).
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (x := inv g a)(y := a)(z:=b) as AssocB.
  specialize assoc_prop with (x := inv g a)(y := a)(z:=c) as AssocC.
  specialize inv_prop with (x := a) as invA.
  specialize id_prop with (x := b) as idB.
  specialize id_prop with (x := c) as idC.
  destruct idB, idC.
  rewrite <- H0, <- H2.
  destruct invA.
  rewrite <- H5.
  rewrite AssocB.
  rewrite AssocC.
  apply (lmult_a).
  trivial.
Qed.



(*Prawo skracania z prawej strony*)
Theorem cancelR: forall (g : Group), forall (a b c : G g), b <* g *> a = c <* g *> a -> b = c.
Proof.
  intros.
  pose (inv_prop := inverse g). (*wprowadzamy do założeń id g, assoc g i inv g*)
  pose (id_prop := id g).
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (z := inv g a)(y := a)(x:=b) as AssocB.
  specialize assoc_prop with (z := inv g a)(y := a)(x:=c) as AssocC.
  specialize inv_prop with (x := a) as invA.
  specialize id_prop with (x := b) as idB.
  specialize id_prop with (x := c) as idC.
  destruct idB, idC.
  rewrite <- H1, <- H3.
  destruct invA.
  rewrite <- H4.
  rewrite <- AssocB.
  rewrite <- AssocC.
  apply (rmult_a).
  trivial.
Qed.


(*Przepisanie jednoznaczności elementu odwrotnego na typ Group*)
Theorem inv_uniq: forall (g : Group), forall (a b: G g), a <* g *> b = e g -> b = inv g a.
Proof.
  intros.
  apply (cancelL g a b (inv g a)).
  pose (inv_prop := inverse g).
  specialize inv_prop with (x := a) as invA.
  destruct invA.
  rewrite H0.
  trivial.
Qed.

(*Twierdzenie o tym, że (a^(-1))^(-1)=a*)
Theorem InvInvAIsA: forall (g : Group), forall (a : G g), inv g (inv g a) = a.
Proof.
  intros.
  pose (inv_prop := inverse g).
  specialize inv_prop with (x := a) as invA.
  destruct invA.
  apply inv_uniq in H0.
  symmetry.
  trivial.
Qed.



(*Twierdzenie o tym, że (ab)^-1=b^-1*a^-1 *)
Theorem InvABEqInvBInvA: forall (g : Group), forall (a b: G g), inv g (a <* g *> b) = inv g b <* g *> inv g a.
Proof.
  intros.
  apply (cancelL g (a <* g *> b)).
  rewrite <- (assoc g).
  pose (inv_prop := inverse g).
  specialize inv_prop with (x := a <* g *> b) as invAB.
  destruct invAB.
  rewrite H.
  specialize inv_prop with (x := b) as invB.
  destruct invB.
  specialize inv_prop with (x := a) as invA.
  destruct invA.
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (x := a)(y := b)(z:=inv g b) as AssocBinv. 
  rewrite AssocBinv.
  rewrite H1.
  pose (id_prop := id g).
  specialize id_prop with (x := a) as idA.
  destruct idA.
  rewrite H6.
  rewrite H3.
  trivial.
Qed.


(* Dowód twierdzenia, że jeśli dla każdego x, y, x^2 = e, to x * y = y * x*)
Theorem pPowerGivesAbelian: forall (g : Group), forall( x y : G g), ( forall (p : G g),  p <* g *>  p = e g ) ->  x <* g *>  y = y  <* g *>  x.
(*  Idea dowódu
xy=(yy)xy(xx)=y(yxyx)x=yx.
 *)
Proof.
  intros.
  specialize H with (p := x) as X.
  specialize H with (p := y) as Y.
  pose (id_prop := id g). (* Wprowadzi nam własność id g do założeń *)
  specialize id_prop with (x := x) as idX.
  specialize id_prop with (x := y) as idY.
  destruct idX, idY.
  rewrite <- H0 at 1.
  rewrite <- H3 at 1.

  rewrite <- Y at 1.
  rewrite <- X at 1.
  (* Wykorzystywanie łączności *)
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (x := y) (y := y) (z := x) as assoc_y.
  rewrite assoc_y.
  specialize assoc_prop with (x := y) (y := x) (z := x) as assoc_x.
  rewrite <- assoc_x.
  specialize assoc_prop with (x := (y <* g *> (y <* g *> x))) (y := (y <* g *> x)) (z := x) as assoc_mul.
    rewrite <- assoc_mul.
    specialize assoc_prop with (x := y) (y :=  (y <* g *> x)) (z := (y <* g *> x)) as assoc_doub.
    rewrite assoc_doub.
    specialize H with (p := (y <* g *> x)) as YX.
   rewrite YX at 1.  
  rewrite H3.
  trivial.
Qed.




Section Z4_Group.

(* Definiujemy typ dla Z4 *)
Inductive Z4 : Type := z0 | z1 | z2 | z3.

(* Definiujemy dodawanie modulo 4 *)
Definition add_Z4 (a b : Z4) : Z4 :=
  match a, b with
  | z0, x => x
  | x, z0 => x
  | z1, z1 => z2
  | z1, z2 => z3
  | z1, z3 => z0
  | z2, z1 => z3
  | z2, z2 => z0
  | z2, z3 => z1
  | z3, z1 => z0
  | z3, z2 => z1
  | z3, z3 => z2
  end.

(* Element neutralny dla dodawania *)
Definition e_Z4 : Z4 := z0.

(* Definiujemy operację odwrotności *)
Definition inv_Z4 (a : Z4) : Z4 :=
  match a with
  | z0 => z0
  | z1 => z3
  | z2 => z2
  | z3 => z1
  end.
  
(* Własność łączności *)
Lemma add_assoc : forall (x y z : Z4),  add_Z4 (add_Z4 x y) z = add_Z4 x (add_Z4 y z).
Proof.
  intros x y z.
  destruct x, y, z;
  simpl;
  reflexivity.
Qed.

(* Lewostronne działanie elementu neutralnego *)
Lemma add_e : forall (x : Z4), add_Z4 e_Z4 x = x /\ add_Z4 x e_Z4 = x.
Proof.
  intros.
  split.
  destruct x; 
  simpl; 
  reflexivity.
  destruct x; 
  simpl; 
  reflexivity.
Qed.


(* Lewostronna odwrotność *)
Lemma add_inv : forall (x : Z4), add_Z4 x (inv_Z4 x) = e_Z4 /\ add_Z4 (inv_Z4 x) x = e_Z4.
Proof.
  intros.
  split.
  destruct x; 
  simpl; 
  reflexivity.
  destruct x; 
  simpl; 
  reflexivity.
Qed.


(*Definicja Z4 jako grupy*)
Definition Z4_Group : Group :=
  {| G := Z4;
     op := add_Z4;
     inv := inv_Z4;
     e := e_Z4;
     assoc := add_assoc;
     id := add_e;
     inverse := add_inv;
  |}.
     

(* Z_2 jest podgrupą Z_4 *)
Definition z0_In_Z2 : In Z4_Group := inSet Z4_Group z0.
Definition z2_In_Z2 : In Z4_Group := inSet Z4_Group z2.
Definition z1_NotIn_Z2 : In Z4_Group := notInSet Z4_Group z1.
Definition z3_NotIn_Z2 : In Z4_Group := notInSet Z4_Group z3.
Definition isInZ2 (z : Z4) : In Z4_Group :=
  match z with
  | z0 => z0_In_Z2
  | z2 => z2_In_Z2
  | z1 => z1_NotIn_Z2
  | z3 => z3_NotIn_Z2
  end.

Lemma Z2_notEmpty : exists (z : Z4), isInZ2 z = inSet Z4_Group z.
Proof.
  exists z0.
  simpl.
  unfold z0_In_Z2.
  reflexivity.
Qed.

Lemma Z2_cInv : forall (z : Z4), isInZ2 z = inSet Z4_Group z -> isInZ2 (inv_Z4 z) = inSet Z4_Group (inv_Z4 z).
Proof.
  intros.
  destruct z.
  simpl.
  unfold z0_In_Z2.
  reflexivity.
  simpl.
  unfold z3_NotIn_Z2.
  discriminate.
  simpl.
  unfold z2_In_Z2.
  reflexivity.
  simpl.
  unfold z1_NotIn_Z2.
  discriminate.
Qed.

Lemma Z2_cOp : forall (x y : Z4), isInZ2 x = inSet Z4_Group x /\ isInZ2 y = inSet Z4_Group y -> isInZ2 (x <* Z4_Group *> y) = inSet Z4_Group (x <* Z4_Group *> y).
Proof.
  intros.
  destruct H.
  simpl.
  destruct x.
  simpl.
  rewrite H0.
  reflexivity.
  destruct y.
  discriminate.
  trivial.
  discriminate.
  trivial.
  destruct y.
  trivial.
  discriminate.
  trivial.
  discriminate.
  destruct y.
  discriminate.
  trivial.
  discriminate.
  trivial.
Qed.

Definition Z2_subGroup_Z4 : SubGroup :=
{|
  Gr := Z4_Group;
  isInH := isInZ2; 
  notEmpty := Z2_notEmpty;
  cInv := Z2_cInv;
  cOp := Z2_cOp
|}.


End Z4_Group.
    

Inductive Z3 : Type := x0 | x1 | x2.

Definition add_Z3 (a b : Z3) : Z3 := 
  match a, b with
  | x0, m => m
  | m, x0 => m
  | x1, x1 => x2
  | x1, x2 => x0
  | x2, x1 => x0
  | x2, x2 => x1
  end.

Definition e_Z3 : Z3 := x0.

Definition inv_Z3 (a : Z3) : Z3 :=
  match a with
  | x0 => x0
  | x1 => x2
  | x2 => x1
  end.

Lemma add_assoc_Z3 : forall (a b c : Z3), add_Z3 (add_Z3 a b) c = add_Z3 a (add_Z3 b c). 
Proof.
  intros.
  destruct a, b, c;
  simpl;
  trivial.
Qed.

Lemma add_e_Z3 : forall (a : Z3), add_Z3 e_Z3 a = a /\ add_Z3 a e_Z3 = a.
Proof.
  intros.
  destruct a;
  split;
  simpl;
  trivial.
Qed.

Lemma add_inv_Z3 : forall (a : Z3), add_Z3 a (inv_Z3 a) = e_Z3 /\ add_Z3 (inv_Z3 a) a = e_Z3.
Proof.
  intros.
  destruct a;
  split;
  simpl;
  trivial.
Qed.

Definition Z3_Group : Group :=
  {| G := Z3;
    op := add_Z3;
    inv := inv_Z3;
    e := e_Z3;
  
    assoc := add_assoc_Z3;
    id :=  add_e_Z3 ;
    inverse :=  add_inv_Z3
  |}.

Theorem add_comm_Z3 : forall (a b : Z3), add_Z3 a b = add_Z3 b a.
Proof.
  intros.
  destruct a, b;
  simpl;
  trivial.
Qed.

Definition Z3_Abelian_Group : AbelianGroup :=
  {| abelGr := Z3_Group;
     comm := add_comm_Z3
  |}.


