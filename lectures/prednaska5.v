(* Prednáška 5
1. čast
- Induktívne definované výroky
- Binárne relácie
- Uzávery (closures)

2. časť
Jazyk NBL
 - Syntax
 - Semantika
 - Typovy system
 - Dôkazy vlastnosti
*)

(*===========================================*)
(**  Induktívne definované výroky           **)
(*===========================================*)

Module inductively. 

(** V Rocq (a všeobecne v logike) 
    induktívne definovaný výrok znamená,
    že daný predikát alebo množina je definovaná pomocou
    pravidiel konštrukcie, ktoré určujú:
    - kedy výrok platí (aké sú základné prípady (base cases)),
    - pravidlá pre odvodenie ďalších prípadov (inductive step).*)

(** Príklad: 
  Induktívna definícia vzťahu menší alebo rovný 

  Dedukčné pravidlá:

          -------------- (le_n)
              n <= n

              n <= m
          -------------- (le_S)
              n <= S m

  Príklad: Dôkaz, že 3 <= 5:

          ---------------- (le_n)
              3 <= 3        
          ---------------- (le_S)
              3 <= 4        
          ---------------- (le_S)
              3 <= 5        
*)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

(* Notácia pre konkrétnu syntax *)
Notation "n <= m" := (le n m) (at level 70).

(* Príklad dôkazu: 3 <= 5 *)
Example le_3_5 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

(* Príklad dôkazu: 2+1 <= 5 *)
Example le_2plus1_5 : 2+1 <= 5.
Proof.
  simpl.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.


(** Príklad:
  Induktívna definícia vzťahu: párne čísla

  Dedukčné pravidlá:

------------ (ev_0)
   even 0


     even n
----------------- (ev_n)
  even (S (S n))        
*)

(* Definícia: n je párne, ak je 0, alebo ak n-2 je párne *)
Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_SS : forall n, even n -> even (S (S n)).

(** Príklad: Dôkaz, že 4 je párne číslo:

    ----------------(ev_0)
        even 0            
    ----------------(ev_n: S (S 0))
        even 2          
    ----------------(ev_n: S (S 2))
        even 4  
*)

(* Príklad dôkazu: 4 je párne *)
Lemma four_is_even : even 4.
Proof.
  (* 4 = S (S 2), 2 = S (S 0) *)
  apply even_SS.
  apply even_SS.
  apply even_O.
Qed.

(*===========================================*)
(** Konštruovanie a dekonštruovanie dôkazov **)
(*===========================================*)

(**
Okrem konštruovania dôkazov, 
že nejaké číslo je párne,
môžeme tieto dôkazy aj rozkladať —
teda uvažovať o tom, ako mohli byť vytvorené.

Definícia predikátu [even] pomocou príkazu [Inductive],
hovorí nielen to, že konštruktory [even_0] a [even_SS]
sú platné spôsoby, ako vytvoriť dôkaz o tom, 
že číslo je párne, ale aj to, 
že sú to jediné dva možné spôsoby,
ako taký dôkaz zostrojiť.
*)

(**
Inými slovami, pre každý dôkaz [E] tvrdenia [even n],
nutne platí jedno z nasledovného:
  - [E = even_0] a teda [n = 0],
  - alebo [E = even_SS n' E'], 
    kde [n = S (S n')] a [E'] je dôkaz pre [even n'].

To znamená, že je možné analyzovať hypotézu tvaru [even n]
podobne, ako iné induktívne definované dátové štruktúry.

Teda existuje spôsob, ako vykonať
analýzu podľa prípadov (case analysis)
alebo indukciu priamo nad štruktúrou dôkazu.
*)

(*===========================================*)
(**  Deštrukcia a inverzia dôkazov          **)
(*===========================================*)

(**
Majme tvrdenie o čísle [n] za predpokladu [even n].

Analýza podľa prípadov môže byť vykonaná nielen na čísle [n] 
pomocou [destruct] alebo [induction], 
ale aj priamo na dôkaze [even n].

Týmto spôsobom sa skúma štruktúra samotného dôkazu, 
nie hodnota čísla.
*)

Theorem even_inversion :
  forall (n : nat),
  even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E.
  - (* E = even_0 : even 0 *)
    left. reflexivity.
  - (* E = even_SS n' E' : even (S (S n')) *)
    right. exists n. split.
    + reflexivity.
    + apply E.
Qed.

(**
  Tento druh viet sa často nazýva 
  inverzné vety (inversion lemmas),
  pretože umožňujú „obrátiť“ dôkaz – získať informáciu o tom,
  ako mohol byť vytvorený.

  V prípade typy even existujú dve možnosti, ako dokázať [even n],
  a inverzná veta ich explicitne vytvori.          .
*)

(*===========================================*)
(**  Použitie inverznej vety v dôkaze       **)
(*===========================================*)

Theorem evSS_ev :
  forall n, even (S (S n)) -> even n.
Proof.
  intros n E.
  apply even_inversion in E.
  destruct E as [H0 | H1].
  - discriminate H0. 
  - destruct H1. 
    destruct H. 
    injection H. 
    intro. 
    rewrite H1. apply H0.       
Qed.
(**
  Inverzná veta v tomto prípade vytvorí dva podcieľe:
  - jeden je kontradikcia,
  - druhý využíva [injection] a [rewrite].
*)


(*===========================================*)
(**  Taktika inversion                      **)
(*===========================================*)

(**
  Rocq poskytuje aj užitočnú taktiku [inversion],
  ktorá vlastnosť inverzie spracuje automaticky —
  netreba ručne dokazovať inverzné vety
  pre každú induktívnu definíciu.
*)

Theorem evSS_ev' :
  forall n, even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E.
  (* Teraz sme v prípade E = even_SS n' E' *)
  apply H0.
Qed.

(**
  Taktika [inversion] dokáže:
  - rozpoznať nemožné prípady (napr. [ev 1]),
  - automaticky unifikovať premenné (napr. [n'] s [n]).
*)

(*===========================================*)
(**  Porovnanie:                            **)
(**  dôkaz s [inversion] a s našou vetou    **)
(*===========================================*)

Theorem one_not_even :
  ~ even 1. 
Proof.
  intros H.
  apply even_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H. destruct H. discriminate H.
Qed.

Theorem one_not_even' :
  ~ even 1.
Proof.
  intros H.
  inversion H.
Qed.


(*===========================================*)
(**  Zhrnutie: Inverzia                     **)
(*===========================================*)
(**
- Každá induktívna definícia v Rocq-u implicitne určuje
  všetky možné spôsoby, ako mohol vzniknúť dôkaz.

- Pomocou [destruct] alebo [inversion] 
  je možné tieto dôkazy analyzovať.

- Taktika [inversion] eliminuje nemožné prípady
  a priamo rozdeľuje hypotézy podľa tvaru dôkazu.

- Je to kľúčový nástroj pri práci s dôkazmi
  o vlastnostiach induktívnych údajových typov.
*)
End inductively. 


(*===========================================*)
(**           Ďalšie taktiky                **) 
(*===========================================*)

(*-------------------------------------------*)
(**           Taktika auto                  **) 

(**
Automatické dokazovanie ([auto]).

Taktika [auto] sa pokúsi vyriešiť cieľ pomocou dostupných 
hypotéz a základných logických pravidiel.

Využíva databázu viet a taktík 
(napr. [intros], [apply], [assumption]) 
a rekurzívne ich kombinuje do hĺbky 
(predvolene do hĺbky 5).

Databázu taktiky možno rozšíriť pomocou [Hint].

  Príklad:
    auto.  (* pokúsi sa vyriešiť cieľ automaticky *)
  
  V prípade, že potrebná vačšia hĺbka je možné 
  pridať parameter:
    auto n.
*)

(* Jednoduchý príklad *)
Lemma auto_example :
  forall (P Q R : Prop),
    P -> Q -> R -> P /\ Q /\ R.
Proof.
  intros P Q R HP HQ HR.
  auto.  
Qed.

(*-------------------------------------------*)
(**     Taktika eauto                       **) 

(**
Rozšírené automatické dokazovanie ([eauto])

Taktika [eauto] rozširuje možnosti [auto] o 
použitie existenčných premenných.  

Pri potrebe dokázať cieľ, ktorý obsahuje 
existenčný kvantifikátor [exists], 
môže [eauto] automaticky zavádzať existenčné 
premenné a pokúsiť sa nájsť ich hodnoty.

Príklad:
  eauto.          (* ako auto, ale s podporou pre existenciu *)
  eauto 6.        (* určuje hĺbku vyhľadávania *)

Taktika využíva rovnakú databázu [Hint] ako [auto].
*)

Example eauto_example :
  forall (P Q : Prop),
    (P -> Q) -> P -> exists x : Prop, x = Q.
Proof.
  intros P Q H HP.
  auto.   (* auto nevyrieši cieľ *)
  eauto.  (* zavádza existenciu a použije H *)
Qed.

(*-------------------------------------------*)
(**     Taktika eapply                      **) 

(**
Taktika [apply] vyžaduje, aby všetky premenné v
aplikovanej vete boli špecifikované.

Taktika [eapply] povoľuje, aby niektoré argumenty
ostali neurčené – Rocq ich následne doplní
počas dôkazu (pomocou unifikácie).

Použitie:
  - [apply lemma] vyžaduje konkrétne argumenty.
  - [eapply lemma] umožní Rocq-u doplniť ich neskôr.

Vhodné, keď je argument odvodený až v ďalšom kroku.
*)

(* 
Theorem eq_trans : forall (A : Type) (x y z : A),
                  x = y -> y = z -> x = z. 
*)

(* Príklad s apply - nutné uviesť argument *)
Lemma ex_eq_trans_apply :
  forall p n m : nat, n = p -> p = m -> n = m.
Proof.
  intros.
  apply eq_trans with (y:= p).
  - apply H.
  - apply H0.  
Qed.

(* Rovnaký dôkaz pomocou eapply *)
(* Príklad s apply - nutné uviesť argument *)
Lemma ex_eq_trans_eapply :
  forall p n m : nat, n = p -> p = m -> n = m.
Proof.
  intros.
  eapply eq_trans.
  - apply H.
  - apply H0.  
Qed.

(*===========================================*)
(**  Binárne relácie                        **)
(*===========================================*)

(**
Binárna relácia na množine X v Rocq 
má typ: X -> X -> Prop.
  
Ide o množinu tvrdení parameterizovanú dvoma prvkami
množiny X, teda tvrdenie o dvojiciach prvkov X.
*)

(* Definícia binárnej relácie *)
Definition relation (X: Type) := X -> X -> Prop.

(**
Príklad binárnej relácie na nat je ≤ (le), 
menej alebo rovné (n1 <= n2).
*)

Print le.
(* Inductive le (n : nat) : nat -> Prop :=
      le_n : n <= n
    | le_S : forall m : nat, n <= m -> n <= S m *)

Check le : nat -> nat -> Prop.
Check le : relation nat.

(* ============================================ *)
(*       Vlastnosti binárnych relácií           *)

(* Reflexívna relácia *)
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

(* Transitívna relácia *)
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, R a b -> R b c -> R a c.

(* Symetrická relácia *)
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, R a b -> R b a.

(* Antisymetrická relácia *)
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, R a b -> R b a -> a = b.

(* Ekvivalencia *)
Definition equivalence {X:Type} (R: relation X) :=
  reflexive R /\ symmetric R /\ transitive R.

(* Čiastočné usporiadanie *)
Definition partialorder {X:Type} (R: relation X) :=
  reflexive R /\ antisymmetric R /\ transitive R.

(* Kváziusporiadanie *)
Definition preorder {X:Type} (R: relation X) :=
  reflexive R /\ transitive R.

(* ============================================ *)
(* Príklad:  
Binárna relácia menší rovný ≤ 
je čiastočne usporiadaná relácia.
*)

Theorem le_reflexive : reflexive le.
Proof.
  unfold reflexive. intro n. apply le_n.
Qed.

Theorem le_trans : transitive le.
Proof.
  unfold transitive. intros n m o Hnm Hmo. 
  induction Hmo.  
  - apply Hnm.
  - apply le_S. apply IHHmo.
Qed.  

(** Pomocná veta pre dôkaz antisymetrie *)
Lemma Sn_le_Sm__n_le_m : 
        forall n m, le (S n) (S m) -> le n m.
Proof.
intros.
inversion H. 
- apply le_n.
- subst. eapply le_trans.
 + apply le_S. apply le_n.
 + apply H1.
Qed.   

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric. induction a.
  - intros. inversion H0. reflexivity.
  - intros. destruct b. 
   + inversion H.  
   + apply Sn_le_Sm__n_le_m in H. 
    apply Sn_le_Sm__n_le_m in H0. f_equal. 
    apply IHa in H; assumption.
Qed.

Theorem le_partialorder : partialorder le.
Proof.
  unfold partialorder. 
  split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.


(*===========================================*)
(**  Uzávery na reláciach                   **)

(*-------------------------------------------*)
(** Tranzitívy uzaver 

  Dedukčné pravidlá:

                R x y          
        ---------------------- (t_step)
            clos_trans R x y

      clos_trans R x y   clos_trans R y z
    ------------------------------------ (t_trans)
              clos_trans R x z
*)

(* Induktívna definícia tranzitívneho uzáveru *)
Inductive clos_trans 
    {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.


(** Príklad použítia tranzitívneho uzáveru 
  Induktívny vzťah "parent_of" 
  a jeho tranzitívny uzaver "ancestor_of".
*)

(* Definícia slovanských bohov *)
Inductive God : Type :=
  | Svarog
  | Perun
  | Dažbog
  | Lada.

(* Induktívna definícia vzťahu rodič *)
Inductive parent_of : God -> God -> Prop :=
  | po_SP : parent_of Svarog Perun
  | po_SD : parent_of Svarog Dažbog
  | po_PL : parent_of Perun Lada.
(*
- Svarog je rodičom Peruna a Dažboga,
- Perun je rodičom Lady 
*)

(* Definícia vzťahu "ancestor_of" ako 
  tranzitívne uzavretie parent_of *)
Definition ancestor_of : God -> God -> Prop :=
  clos_trans parent_of.

(**
  Dôkaz, že Svarog je predkom Lada:

---------------------(po_SP)   ------------------------(po_PL)
 parent_of Svarog Perun           parent_of Perun Lada
-----------------------(t_step) -----------------------(t_step)
ancestor_of Svarog Perun         ancestor_of Perun Lada
------------------------------------------------------(t_trans)
          ancestor_of Svarog Lada 
*)
Example ancestor_of_ex : ancestor_of Svarog Lada.
Proof.
  unfold ancestor_of.
  apply t_trans with Perun.
  - apply t_step. apply po_SP.
  - apply t_step. apply po_PL.
Qed.

(*--------------------------------------------*)
(** Reflexívny a tranzitívny uzáver

  Dedukčné pravidlá:

             R x y           (rt_step)
        ---------------------
          clos_refl_trans R x y

             x                (rt_refl)
        ---------------------
          clos_refl_trans R x x

  clos_refl_trans R x y   clos_refl_trans R y z
----------------------------------------------- (rt_trans)
          clos_refl_trans R x z
*)

(* Induktívna definícia: reflexívny a tranzitívny uzáver *)
Inductive clos_refl_trans 
  {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

(** Príklad: 
  Reflexívny a tranzitívny uzáver relácie R
  pre množinu A = {1,2,3} a R = {(1,2), (2,3)}
*)

(* Definícia relácie R *)
Definition R (x y : nat) : Prop :=
  (x = 1 /\ y = 2) \/ (x = 2 /\ y = 3).

(* Definícia relácie R medzi prirodzenými číslami x a y.
   Relácia R x y je pravdivá, ak platí buď:
     - x = 1 a y = 2, alebo
     - x = 2 a y = 3.
   
   Vstupy: x, y : nat

   Množina hodnôt, pre ktoré R je pravdivá:
     {(1,2), (2,3)} 
*)
Example R_example1 : R 1 2.
Proof. 
  unfold R.
  left. split; reflexivity.
Qed.

Example R_example2 : R 2 3.
Proof.
  right. split; reflexivity.
Qed.

Example R_example3 : ~ R 1 3.
Proof.
  unfold not. intros H.
  destruct H as [[H1 H2] | [H1 H2]]; discriminate.
Qed.


(* Reflexívny a tranzitívny uzáver relacie R *)
Definition R_refl_trans := clos_refl_trans R.

(** 
Množina hodnôt, pre ktoré R_refl_trans je pravdivá:
    {(1,1), (2,2), (3,3), (1,2), (2,3), (1,3)} 
*)

(* Reflexívny uzáver: 
  každý prvok je v relácii sám so sebou *)
Example refl_1 : R_refl_trans 1 1.
Proof.
  apply rt_refl.
Qed.

Example refl_2 : R_refl_trans 2 2.
Proof.
  apply rt_refl.
Qed.

Example refl_3 : R_refl_trans 3 3.
Proof.
  apply rt_refl.
Qed.

(* Tranzitívny uzáver: kombinujeme existujúce páry *)
Example trans_1_2 : R_refl_trans 1 2.
Proof.
  apply rt_step. left. split; reflexivity.
Qed.

Example trans_2_3 : R_refl_trans 2 3.
Proof.
  apply rt_step. right. split; reflexivity.
Qed.

Example trans_1_3 : R_refl_trans 1 3.
Proof.
  apply rt_trans with 2.
  - apply rt_step. left. split; reflexivity.
  - apply rt_step. right. split; reflexivity.
Qed.

(*============================================*)
(** NBL: Jazyk čísel a pravdivostných hodnôt **)
(*============================================*)
Module nbl.

(*===========================================*)
(**         Úvod k jazyku NBL               **)
(*===========================================*)

(**
Jazyk NBL je minimalistický jazyk, ktorý kombinuje:
- booleovské hodnoty (`true`, `false`),
- prirodzené čísla (`0`, `succ`, `pred` , `iszero`),
- a základné podmienené výrazy (`if ... then ... else ...`).

V systéme Rocq formálne zadefinujeme a analyzujeme:
- syntaktickú štruktúru programu (ako sa termy skladajú),
- sémantiku (ako sa termy vyhodnocujú krok za krokom),
- typový systém, ktorý zaručuje,
  že „správne typovaný program sa nikdy nezasekne“.
- a formálne dokážeme bezpečnosť navhrnutého jazyka.

Postup:

1. Syntax jazyka NBL
   - Definícia termov a notácie
   - Príklady konštrukcie jednoduchých výrazov

2. Sémantika (vyhodnocovanie)
   - Relácia malých krokov (`t → t'`)
   - Viackrokové vyhodnocovanie (`t →* t'`)
   - Normálne formy

3. Typový systém
   - Typy: `Bool` a `Nat`
   - Typové pravidlá
   - Príklady typovania

4. Kanonické hodnoty a základné vety
   - Veta o jednoznačnosti typu
   - Vety o kanonických hodnotách

5. Bezpečnosť jazyka (type soundness)
   - Veta o progresii
   - Veta o zachovaní typu (preservation)
*)


(*--------------------------------------------*)
(** Syntax jazyka NBL                         *)
(*--------------------------------------------*)
(* 
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
*)

Inductive nbl : Type := 
| tru : nbl
| fls : nbl
| zro : nbl
| iszro : nbl -> nbl
| prede : nbl -> nbl
| scc : nbl -> nbl
| ite : nbl -> nbl -> nbl -> nbl.


Definition p := tru.
Print p.

(*--------------------------------------------*)
(** Notácia pre konkrátnu syntax              *)
(*--------------------------------------------*)
(*
  - notácia ako v NBL,
  - potrebný vlastný rozsah (scope), 
  - prepis štandardných notácii z Rocq*)

(*--------------------------------------------*)
(** Notácia pre konkrátnu syntax              *)
(** (pozmenená oproti prednáške)              *)
(*--------------------------------------------*)

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := 
  (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := 
  false (at level 1): tm_scope.
Notation "'false'" := 
  (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := 
  e (e custom tm at level 99): tm_scope.
Notation "( x )" := 
  x (in custom tm, x at level 99): tm_scope.
Notation "x" := 
  x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := 
  (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 
  0 (at level 1): tm_scope.
Notation "'succ' x" := 
  (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := 
  (prede x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := 
  (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := 
  (ite c t e)
    (in custom tm at level 90, c custom tm at level 80,
    t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(**
Z dôvodu miešania sa NBL notácie s typom bool 
a operáciami nad ním, budeme termy NBL zapisovať  
využitím konkrétnej syntaxe v zátvorkách <{ t }>. 

Taktiež je možné využiť abstraktnú syntax 
z induktívnej definície typu nbl.
*)


(** Príklady zapisu termov: *)
Check true.         (* true : bool *)
Check <{ true }>.   (* <{ true }> : nbl *)
Check tru.          (* <{ true }> : nbl *)

Definition p1 := <{ if true then 0 else true }>.
Check p1.   (* p1 : nbl *)
Definition p2 :=  if true then 0 else 1.
Check p2.   (* p2 : nbl *)
Definition p3 := ite tru zro tru.  
Check p3.   (* p3 : nbl *)


(*--------------------------------------------*)
(** Hodnoty jazyka NBL                        *)
(*--------------------------------------------*)

(* Hodnoty sú true, false, alebo numerické hodnoty:
   v  ::= true | false | nv
   nv ::= 0 | succ nv 
*)

Inductive bval : nbl -> Prop := 
| bvtrue : bval tru
| bvfalse : bval fls.

Inductive nval : nbl -> Prop := 
| nv0 : nval zro
| nvscc : forall t, nval t -> nval (scc t).

(** Normálna forma termov je hodnota *)
Definition value (t : nbl) := nval t \/ bval t.


(*--------------------------------------------*)
(** Štrukturálna operačná sémantika           *)
(*--------------------------------------------*)
(*  Nazývaná aj sémantika malých krokov
    (small step semantics).

    Vyhodnocovacia relácia:
      -----------------
      |    t -> t'    |
      -----------------

    Vyhodnocovacie pravidlá:

----------------------------------- (st_iftrue)
if true then t1 else t2 --> t1

----------------------------------- (st_iffalse)
if false then t1 else t2 --> t2	

                   t1 --> t1'
--------------------------------------------------- (st_if)
if t1 then t2 else t3 --> if t1' then t2 else t3

      t1 --> t1'
--------------------- (st_succ)
 succ t1 --> succ t1'

---------------- (st_pred0)
 pred 0 --> 0

  numeric value v	
--------------------- (st_predsucc)
pred (succ v) --> v

     t1 --> t1'
--------------------- (st_pred)
pred t1 --> pred t1'

------------------- (st_iszero0)
 iszero 0 --> true

       numeric value v
--------------------------- (st_iszeronv)
 iszero (succ v) --> false

       t1 --> t1'
------------------------- (st_iszero)
iszero t1 --> iszero t1'	

*)

(*
Reserved Notation "t '-->' t'" (at level 40).
Inductive smallstep : nbl -> nbl -> Prop :=
| st_iftrue : forall t1 t2, 
    <{ if true then t1 else t2 }> --> <{ t1 }> 
| st_iffalse : forall t1 t2, 
    <{ if false then t1 else t2 }> --> <{ t2 }> 
| st_if : forall t1 t2 t3 t1', 
                         t1 --> t1' ->
  <{ if t1 then t2 else t3 }> --> <{ if t1' then t2 else t3 }>       
| st_succ : forall t t', 
              t --> t' ->
    <{ succ t }> --> <{ succ t' }>  
| st_pred0 : 
    <{ pred 0 }> --> <{ 0 }>  
| st_predsucc : forall v, nval v -> 
    <{ pred (succ v) }>  -->  <{ v }> 
| st_pred : forall t t', 
    <{ pred t }> --> <{ pred t' }>  
| st_iszero0 : 
    <{ iszero 0 }> --> <{ true }>  
| st_iszeronv : forall v, nval v -> 
    <{ iszero (succ v) }>  -->  <{ false }> 
| st_iszero : forall t t', 
          smallstep t t' -> 
    <{ iszero t }> --> <{ iszero t' }>   

where "t '-->' t'" := (smallstep t t').
Hint Constructors smallstep : core.
*)

Reserved Notation "t '-->' t'" (at level 40).
Inductive smallstep : nbl -> nbl -> Prop :=
  | st_iftrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | st_iffalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | st_if : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | st_succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | st_pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | st_predsucc : forall v,
      nval v ->
      <{ pred (succ v) }> --> v
  | st_pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | st_iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | st_iszeronv : forall v,
       nval v ->
      <{ iszero (succ v) }> --> <{ false }>
  | st_iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
where "t '-->' t'" := (smallstep t t').
Hint Constructors smallstep : core.


(** Poznámka:

  Príkaz [Hint Constructors step : core.] definuje, že všetky 
  konštruktory induktívnej relácie [smallstep]
  sa majú automaticky používať pri taktikách [auto] a [eauto].

  V praxi to znamená, pri pokuse o dokáz tvrdenia v tvare
       [t --> t']
  (teda že [t] vykoná malý krok na [t']), 
  Rocq sa pokúsi sám nájsť vhodný konštruktor ako napríklad 
  [st_iftrue], [st_predsucc], [st_iszero], atď.

*)

(** Príklady: *)
Theorem ex1: 
  <{if true then succ 0 else succ 0 }> --> <{ succ 0 }>.
Proof.
apply st_iftrue.
Qed.

Print ex1.

Theorem ex1_auto: 
  <{if true then succ 0 else succ 0 }> --> <{ succ 0 }>.
Proof.
auto.
Qed.
Print ex1_auto.


(*---------------------------------------------*)
(** Reflexívno-tranzitívny uzáver (multi-step) *)
(*---------------------------------------------*)

Inductive multistep : nbl -> nbl -> Prop :=
  | multi_refl : forall t, multistep t t  
  | multi_tran : forall t1 t2 t3,
      smallstep t1 t2 ->  
      multistep t2 t3 ->
      multistep t1 t3.

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors multistep : core.

(** Príklady: *)
Example ex_multistep : 
  multistep <{(if true then pred 0 else 0)}> <{0}>.
Proof.
apply multi_tran with (t2 := <{pred 0}>).
- apply st_iftrue.
- apply multi_tran with (t2 := <{0}>).
 + apply st_pred0.
 + apply multi_refl.
Qed. 
Print ex_multistep.

Example ex_multistep_eauto : 
  multistep <{(if true then pred 0 else 0)}> <{0}>.
Proof.
  eauto.
Qed. 
Print ex_multistep.
Print ex_multistep_eauto.

Print ex_multistep.

Example ex_multistep_eapply : 
  <{if true then pred 0 else 0}> -->* <{0}>.
Proof.
eapply multi_tran .
- apply st_iftrue.
- eapply multi_tran .
 + apply st_pred0.
 + apply multi_refl.
Qed. 

(*--------------------------------------------*)
(** Normálne formy                            *)
(*--------------------------------------------*)
Definition normal_form (t : nbl) : Prop :=
   ~exists t', smallstep t t'.

(** Príklad: *)
Theorem ex_normal_form_not_true : 
~(normal_form <{iszero 0}>).
Proof.
  unfold normal_form.
  intros H.
  apply H.
  exists <{true}>.
  apply st_iszero0.   
Qed.


(*--------------------------------------------*)
(** Typový systém                             *)
(*--------------------------------------------*)
(*

    Typová relácia:
      -----------------
      |     t:T       |
      -----------------

    Typové pravidlá:


-------------------- (t_true)
  |-- true: Bool	


-------------------- (t_false)
  |-- false: Bool	


|-- t1: Bool    |-- t2: T    |-- t3: T	(T_If)  
------------------------------------------------- (t_if)
        |-- if t1 then t2 else t3: T	


------------------ (t_0)
  |-- 0: Nat	


    |-- t1: Nat
--------------------- (t_succ)
  |-- succ t1: Nat	


    |-- t1: Nat
--------------------- (t_pred)
  |-- pred t1: Nat	


    |-- t1: Nat
------------------------ (t_iszero)
  |-- iszero t1: Bool	
*)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Declare Custom Entry ty.
Notation "'Nat'" := Nat (in custom ty).
Notation "'Bool'" := Bool (in custom ty).
Notation "x" := x (in custom ty, x global).

Reserved Notation "<{ '|--' t 'of' T }>"
            (at level 0, t custom tm, T custom ty).

Inductive typed : nbl -> ty -> Prop :=
  | t_true : 
       <{ |-- true of Bool }>
  | t_false :
       <{ |-- false of Bool }>
  | t_if : forall t1 t2 t3 T,
       <{ |-- t1 of Bool }> ->
       <{ |-- t2 of T }> ->
       <{ |-- t3 of T }> ->
       <{ |-- if t1 then t2 else t3 of T }>
  | t_0 :
       <{ |-- 0 of Nat }>
  | t_succ : forall t1,
       <{ |-- t1 of Nat }> ->
       <{ |-- succ t1 of Nat }>
  | t_pred : forall t1,
       <{ |-- t1 of Nat }> ->
       <{ |-- pred t1 of Nat }>
  | t_iszero : forall t1,
       <{ |-- t1 of Nat }> ->
       <{ |-- iszero t1 of Bool }>

where "<{ '|--' t 'of' T }>" := (typed t T).
Hint Constructors typed : core.

(** Príklady: *)
Theorem ex3: <{ |-- true of Bool }>.
Proof. 
apply t_true.
Qed.

Theorem ex4: 
<{|-- if true 
        then (if iszero 0 then true else false ) 
        else true of Bool }>.
Proof.
apply t_if.
- apply t_true.
- apply t_if.
  + apply t_iszero. apply t_0. 
  + apply t_true.
  + apply t_false. 
- apply t_true. 
Qed.

Theorem ex4_eauto: 
<{|-- if true 
        then (if iszero 0 then true else false ) 
        else true of Bool }>.
Proof.
eauto.
Qed.


Theorem ex5 :
  ~ <{ |-- if false then 0 else true of Bool }>.
Proof.
unfold not.
intros.
inversion H.
inversion H5. 
Qed.


(**
-------------------------------------------------------
     ZÁKLADNÉ VLASTNOSTI TYPOVÉHO SYSTÉMU
-------------------------------------------------------

V dobre navrhnutom typovom systéme 
by mali platiť tri kľúčové vlastnosti:

1. Jednoznačnosť typu (Uniqueness of Types)

    Ak  Γ ⊢ t : T₁  a  Γ ⊢ t : T₂,
    potom  T₁ = T₂.

    - Každý výraz má v danom prostredí práve jeden typ.
      Typovanie je teda deterministické a konzistentné.

    - Význam:
      - Zjednodušuje dôkazy o správnosti.
      - Zaručuje, že kompilátor alebo typová kontrola
        sa „nerozhoduje“ medzi rôznymi typmi
        toho istého výrazu.


2.  Progres (Progress Theorem)**

    Ak ⊢ t : T,
    potom buď:
    - t je už hodnota (value), alebo
    - existuje t', také že t --> t'.

    - Dobre typovaný výraz sa nikdy „nezasekne“.
      Buď už predstavuje hodnotu, 
      alebo sa dá ďalej vyhodnocovať.

    - Význam:
      - Dobre typované programy nespadnú na runtime chybe typu.
      - Typový systém zachytáva chyby ešte pred spustením programu.

3.  Stabilita (zachovanie) typu (Preservation Theorem)

    Ak ⊢ t : T  a  t --> t',
    potom  ⊢ t' : T.

    - Typ sa počas vykonávania programu nezmení.

    - Význam:
      - Každý krok výpočtu zachováva typovú korektnosť.
      - Typový systém a sémantika sú v súlade.

    - Príklad:
      - Ak <{ t }> má typ Nat a <{ t --> t' }>,
      - potom aj <{ t' }> má typ Nat.


Spolu tieto dve vety – [Progress] a [Preservation] – 
tvoria dôkaz o typovej korektnosti (bezpečnosti jazyka) 
(z ang. Type Soundness)
      
        "Dobre typované programy sa nikdy nezaseknú
         a počas behu si zachovávajú správny typ."
-------------------------------------------------------
*)


(*--------------------------------------------*)
(** Veta o jednoznačnosť typu                 *)
(*--------------------------------------------*)

(*
  Teoretické znenie:
    Ak výraz [t] má typ [T1] aj typ [T2], potom tieto typy musia byť rovnaké.

  Formálne:
      <{ |-- t of T1 }>  /\  <{ |-- t of T2 }>  ->  T1 = T2.

  Dôkaz prebieha štrukturálnou indukciou nad tvarom termu [t].
*)
Theorem type_uniqueness: forall t T1 T2, 
        <{ |-- t of T1 }> /\ <{ |-- t of T2 }> -> T1 = T2.
Proof.
  intros.
  destruct H as [HT1 HT2].   
  (* rozdelíme konjunkciu na dva predpoklady *)
  induction t. 
  (* dôkaz indukciou podľa štruktúry termu t *)
  - (* prípad: t = true *)
    inversion HT1. inversion HT2. reflexivity.
    (** využitím vety o inverzii odvodíme, 
        že ak  <{ |-- true of T }>, tak T je Bool*)
  - (* prípad: t = false *)
    inversion HT1. inversion HT2. reflexivity.
    (** rovnaké zdôvodnenie ako vyššie *)
  - (* prípad: t = 0 *)
    inversion HT1. inversion HT2. reflexivity.
    (** nula má vždy typ [Nat]. *)
  - (* prípad: t = succ t1 *)
    inversion HT1. inversion HT2. reflexivity.
    (** inverzia na typovom pravidle pre iszero, 
        potom T musí Nat *)
  - (* prípad: t = pred t1 *)
    inversion HT1. inversion HT2. reflexivity.
    (** rovnaké zdôvodnenie ako vyššie *)
  - (* prípad: t = iszero t1 *)
    inversion HT1. inversion HT2. reflexivity.
    (** test [iszero] má vždy výsledok typu [Bool]. *)
  - (* prípad: t = if t1 then t2 else t3 *)
    inversion HT1; subst.
    inversion HT2; subst.
    apply IHt2; assumption.
Qed.

(** Kratší dôkaz*)
Theorem type_uniqueness': forall t T1 T2, 
        <{ |-- t of T1 }> /\ <{ |-- t of T2 }> -> T1 = T2.
Proof.
intros.
destruct H as [HT1 HT2].
induction t; inversion HT1; inversion HT2; try reflexivity.
(** Vyriešných prvých 6 prípadov, ostal prípad pre IF *)
- inversion HT1; subst.
  inversion HT2; subst.
  apply IHt2. 
  assumption.
  assumption.
Qed.

(*--------------------------------------------*)
(** Vety o kanonických hodnotách              *)
(*--------------------------------------------*)
(**
  Tieto vety sú kľúčovým medzičlánkom medzi 
  typovým systémom a semantikou hodnôt.

  Ich úlohou je formálne zachytiť nasledujúcu intuitívnu myšlienku:

  Ak je výraz dobre typovaný a je zároveň hodnotou,
  potom musí mať určitý „kanonický“ (štandardný) tvar
  zodpovedajúci jeho typu.

  Inými slovami:
    - Hodnota typu [Bool] musí byť buď [true] alebo [false].
    - Hodnota typu [Nat] musí byť [0] alebo [succ n], 
      kde [n] je číselná hodnota.
*)

(*--------------------------------------------*)
(** Veta [bool_canomical]                     *)
(*--------------------------------------------*)

Lemma bool_canomical : forall t, 
      <{|-- t of Bool}> /\ value t -> bval t.
Proof.
  intros.
  unfold value in H.            
  (* rozbalíme definíciu hodnoty *)
  destruct H as [Ht Hbv].       
  (* rozdelíme konjunkciu typovej relácie
    a výroku, že t je hodnota *)
  destruct Hbv as [Hnv | Hbv].       
  (* hodnota môže byť nval alebo bval *)
  - inversion Hnv. subst.
    + inversion Ht.                  
    (* t = 0, ale 0 má typ Nat, nie Bool *)
    + subst. inversion Ht.
    (* t = succ t má typ Nat, nie Bool *)
  - apply Hbv.                       
  (* t boolean hodnota *)
Qed.


(*--------------------------------------------*)
(** Veta [nat_canomical]                      *)
(*--------------------------------------------*)

(** Analogický postup ako v predchadzajúcom prípade *)
Lemma nat_canomical : forall t, 
      <{|-- t of Nat}> /\ value t -> nval t.
Proof.
  intros.
  destruct H as [Ha Hb].
  unfold value in Hb.
  destruct Hb as [Hnv | Hbv].
  - apply Hnv.                       
  (* ak je t číselná hodnota, hotovo *)
  - inversion Hbv. subst.
    inversion Ha. subst.
    inversion Ha.
Qed.


(*--------------------------------------------*)
(**     Dôkaz bezbečnosti jazyka NBL:         *)
(**     Veta o progresii a stabilite          *)
(*--------------------------------------------*)
(* 
------------------------------------------------
  VETA O PROGRESE (Progress Theorem)
------------------------------------------------

Ak ⊢ t : T (t. j. výraz t je dobre typovaný),
potom buď:
  - t je hodnota (value), alebo
  - existuje t', také že t --> t' (t je možné redukovať).

  Dobre typovaný program sa pri vykonavaní nikdy "nezasekne" – 
   - buď je hodnota,
   - alebo sa dá ďalej vyhodnocovať.
*)

Theorem progress: forall t T, 
        <{ |-- t of T}> -> (value t) \/ exists t', (t --> t').
Proof.
intros.
(** Dôkaz indukciou nad typovou reláciou *)
induction H. 

  (** true *)
- left. unfold value. right. apply bvtrue.

  (** false *)
- left. unfold value. right. apply bvfalse.
  
  (** if t1 then t2 else t3  *)
- right. destruct IHtyped1. 
  + assert (Hb : bval t1).
    { apply (bool_canomical t1). split; assumption. } 
    inversion Hb. subst.  
    * exists t2. apply st_iftrue.
    * exists t3. apply st_iffalse.  
  + destruct H2 as [t1' Hstep]. 
    exists (<{if t1' then t2 else t3}>). 
    apply st_if. assumption.
  
  (** 0 *)
- left. unfold value. left. apply nv0.
  
  (** succ t1 *)
- destruct IHtyped. 
 + left. assert (nval t1) as Hn.
    { apply (nat_canomical t1). 
      split. apply H. apply H0. }
    unfold value. left. apply nvscc. apply Hn.
 + right. destruct H0 as [t' Hstep]. 
   exists (scc t'). 
   apply st_succ. apply Hstep.
  
  (** pred t1 *)
- destruct IHtyped as [Hv | [t' Hstep]]. 
  + destruct (nat_canomical t1). 
    split. assumption. assumption. 
    right. exists zro. apply st_pred0.   
    right. exists t. apply st_predsucc. assumption.
  + right. exists (prede t'). apply st_pred. assumption.
  
  (** iszero t1 *) 
- destruct IHtyped as [Hv | [t' Hstep]]. 
 + destruct (nat_canomical t1). split. 
    * assumption.
    * assumption.
    * right. exists tru. apply st_iszero0.
    * right. exists fls. apply st_iszeronv. assumption.
 + right. exists (iszro t'). apply st_iszero. assumption.
Qed.  

(**
-------------------------------------------------------
 VETA O STABILITE (ZACHOVANÍ) TYPU (Type Preservation)
-------------------------------------------------------

Formulácia:
  Ak výraz [t] má typ [T] a vykoná jeden krok redukcie na [t'],
  potom aj [t'] má typ [T]:

    ⊢ t : T  /\  t --> t'  →  ⊢ t' : T

Typový systém je konzistentný so sémantikou: každý krok redukcie
zachováva typ. Správne typovaný program nikdy „nestratí“ svoj typ
počas vykonávania.

Túto vetu je možné dokázať dvomi spôsobmi:
  1. Indukciou na typovej relácii.
  2. Indukciou na vyhodocovacej relácii.
*)

(** Indukcia na typovej relácii: *)
Theorem preservation: forall t t' T, 
        <{|-- t of T}> /\ (t-->t') ->  <{|-- t' of T}>.
intros.
destruct H. 
(** rozdelenie konjunkcie na typová a vyhodnocovaciu reláciu *)
generalize dependent t'.
induction H; intros t' Hstep; 
inversion Hstep; subst; try assumption.
(* if-true/false *)
- apply t_if.
  + apply IHtyped1. assumption.
  + assumption.
  + assumption.
(* succ *)
- apply t_succ. apply IHtyped in H1. assumption. 
(* pred 0 *)
- inversion H. assumption.
(* pred *)
- apply t_pred. apply IHtyped. assumption. 
(* true *)
- apply t_true. 
(* false *)
- apply t_false.
(* iszero *)
- apply t_iszero. apply IHtyped. apply H1.
Qed.

(** Indukcia na vyhodnocovacej relácii: *)
Theorem preservation': forall t t' T, 
        <{|-- t of T}> /\ (t-->t') ->  <{|-- t' of T}>.
intros.
destruct H as [Ht Hr].
generalize dependent T.
induction Hr.
(** Dokončte dôkaz *)
Admitted.

End nbl.
