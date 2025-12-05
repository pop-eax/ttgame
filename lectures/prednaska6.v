(*  Prednáška 6
1. čast
Údajové štruktúry:
- maps
- partial maps

2. časť
Jednoducho typovaný lambda kalkul s Bool 
 - Syntax
 - Sémantika
 - Typový systém
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Export Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
Require Import String.
Open Scope string_scope.
Import ListNotations.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Set Default Goal Selector "!".


(*============================================*)
(** 1. časť:                                 **)
(** Údajové štruktúry: Maps a Partial maps   **)
(*============================================*)

Module maps.
(* -------------------------------------- *)
(*         Identifikátory                 *)

(** 
Na indexovanie kľúčov v zobrazeniach (mapách) bude použitý typ String. 
*)

(** Porovnávanie reťazcov a reflexia v Rocq
1. Porovnávanie reťazcov:
   - `String.eqb x y`        : boolean test (true, ak x = y)
   - `String.eqb_refl x`     : x =? x = true
   - `String.eqb_eq n m`     : (n =? m) = true <-> n = m
   - `String.eqb_neq n m`    : (n =? m) = false <-> n <> m

2. Reflexia (`reflect`):
   - `reflect P b` spája booleovskú hodnotu `b` s logickým výrokom `P`
     - `reflect P true`  => platí P
     - `reflect P false` => platí ~P
   - Reflection lemma pre reťazce: 
       
      Check String.eqb_spec :
         forall x y : string, reflect (x = y) (String.eqb x y)
     
     => umožňuje prejsť z Boolean testu na logický dôkaz

3. Použitie v dôkazoch:
   (* klasické použitie: Boolean -> Prop *)
   apply String.eqb_eq. 
   
   (* S reflect: získame rozdelenie prípadov automaticky *)
   destruct (String.eqb_spec s1 s2) as [Heq | Hneq].
     - Heq  : s1 = s2
     - Hneq : s1 <> s2

4. Výhoda reflexie:
   - Efektívne kombinovanie výpočtov (bool) a dôkazov (Prop)
*)

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.

Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.

Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.

Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).

(** Príklad *)

Example test_eqb_spec1 :
  String.eqb "foo" "foo" = true.
Proof.
  reflexivity.
Qed.

Example test_eqb_spec2 :
  String.eqb "foo" "bar" = false.
Proof.
  reflexivity.
Qed.

(* Použitie reflect *)
Lemma eqb_reflect_example : forall s1 s2 : string,
  (String.eqb s1 s2 = true) -> s1 = s2.
Proof.
  intros s1 s2 H.
  apply String.eqb_eq.
  apply H.
Qed.

Lemma eqb_reflect_example2 : forall s1 s2 : string,
  (String.eqb s1 s2 = true) -> s1 = s2.
Proof.
  intros s1 s2 H.
  (* získame reflect dôkaz *)
  destruct (String.eqb_spec s1 s2) as [Heq | Hneq].
  - (* prípad x = y *)
    apply Heq.
  - (* prípad x <> y, ale to nemôže nastať *)
    discriminate H.
Qed.


(* ====================================== *)
(*         Úplné zobrazenia               *)
(* ====================================== *)

(** Total maps (úplné zobrazenia) 

Úplné zobrazenie je funkcia z kľúčov do hodnôt, 
ktorá vždy vracia hodnotu, aj keď kľúč nie je explicitne definovaný.
*)

(* Total map: každému kľúču priradíme hodnotu typu A *)
Definition total_map (A : Type) := string -> A.

(* Prázdna total map – všetky kľúče vracajú default hodnotu *)
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(* Aktualizácia úplného zobrazenia,
ktoré berie zobrazenie [m], kľúč [x] a hodnotu [v] 
a vracia nové zobrazenie, 
ktorá priradí [x] hodnotu [v] a každý iný kľúč 
spracuje podľa pôvodného zobrazenia [m].
*)
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

(* --------------------------------------------- *)
(* Úplne zobrazenie ako zoznam s konštruktormi   *)

(** total_map môžeme chápať podobne ako zoznam, 
    ktorý obsahuje všetky možné kľúče, pričom:

    - Každý prvok zoznamu je párom (kľúč, hodnota).
    - Existuje základný konštruktor t_empty, 
      ktorý inicializuje mapu na jednu predvolenú hodnotu 
      pre všetky kľúče.
    - Ďalší konštruktor je t_update, 
      ktorý pridá alebo prepíše hodnotu pre konkrétny kľúč.

Formálne:

  t_empty v       -- zobrazenie, kde každý kľúč má hodnotu v
  t_update m x v  -- zobrazenie, rozširuje m o x ↦ v

Teda:

  t_empty ≈ [] (prázdny zoznam, všetko default)
  t_update ≈ cons (kľúč, hodnota) ... 
            (pridá nový pár alebo prepíše existujúci)
*)

(** Príklad: *)
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.
(* 
Predstavme si examplemap ako 
"zoznam aktualizácií nad základnou hodnotou false":

examplemap ≈ [
  ("bar", true);   -- posledná aktualizácia
  ("foo", true)    -- predchádzajúca aktualizácia
] + default: false

Interpretácia:
- Hodnota "bar" -> true
- Hodnota "foo" -> true
- Každý iný kľúč -> false (z t_empty false)
*)

(* -------------------------------------- *)
(* Notácie pre Total map                  *)

(** Prázdne zobrazenie s predvolenou hodnotou. *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** Aktualizácia zobrazenia *)
Notation "x '!->' v ';' m" := 
        (t_update m x v)
        (at level 100, x constr, right associativity).

(** 
Predchádzajúci príklad [examplemap] 
prostredníctvom novej notácie: 
*)
Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(** Týmto sme dokončili definíciu úplných máp.  Poznámka: nie je
    potrebné definovať operáciu [find] pre túto reprezentáciu máp,
    pretože stačí aplikovať funkciu! *)

Compute (examplemap' "foo").
(* = true : bool *)
Compute (examplemap' "bar").
(* = true : bool *)
Compute (examplemap' "baz").
(* = false : bool *)

Example update_example1 : examplemap' "baz" = false.
Proof.  reflexivity. Qed.
Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.
Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.
Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.


(* ====================================== *)
(*        Čiastočné zobrazenia            *)
(* ====================================== *)

(** Partial maps (čiastočné zobrazenia)

(** Nakoniec definujeme _čiastočné mapy_ na základe úplných máp.
    Čiastočná mapa s prvkami typu [A] je úplná mapa s
    prvkami typu [option A] a predvoleným prvkom [None]. *)
*)

(* Partial map: nie každý kľúč musí mať hodnotu *)
Definition partial_map (A : Type) := total_map (option A).

(* Prázdna partial map – žiadny kľúč nemá hodnotu *)
Definition empty {A : Type} : partial_map A :=
  t_empty None.

(* Aktualizácia partial mapy *)
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** Notácia pre aktualizáciu zobrazenia: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

(** Schovanie posledného prvku zobrazenia (prázdneho) *)
Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

(** Príklad: *)
Definition examplepmap :=
(   "Church"  |-> true ; 
    "Turing"  |-> false;
    "Godel"   |-> false;
    "Gentzen" |-> true
).

Compute examplepmap "Church".

Example ex1 : (examplepmap "Church" = Some true). 
Proof.
 unfold examplepmap. 
 unfold update. 
 unfold empty. 
 unfold t_update.
 simpl. reflexivity.
Qed.

Example ex2 : (examplepmap "Godel" = Some false). 
Proof.
 reflexivity.
Qed.

(*===================================================*)
(** Pomocné vety o zobrazeniach                      *)
(*===================================================*)

(** V dôkazoch vlastností jednoducho typovaného lambda kalkulu 
    bude často vhodné aplikovať niektorú z nasledujúcich viet. 

    Pre ich dôkaz niektorých z nich bude potrebné použiť axiómu:
    [functional_extensionality] z knižnice:
    
    From Stdlib Require Import FunctionalExtensionality.
*)

Print functional_extensionality.

(* ====================================== *)
(*        Functional Extensionality       *)
(* ====================================== *)

(** Logika v systéme Rocq je minimalistická. 
    To znamená, že niektoré intuitívne matematické tvrdenia 
    nie je možné dokázať bez pridania axióm. *)

(** Príklad: porovnanie dvoch funkcií *)
Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof.
  reflexivity.
Qed.

(** Vo všeobecnosti považujeme dve funkcie f a g za rovnaké, 
    ak produkujú rovnaký výstup pre každý vstup: 

      (forall x, f x = g x) -> f = g
    
    Tento princíp sa nazýva *functional extensionality*. 
*)

(** Avšak, functional extensionality 
    nie je súčasťou základnej logiky Rocq. 
*)
Example function_equality_ex2 :
  (fun x => x + 1) = (fun x => 1 + x).
Proof.
  Fail reflexivity.          (* reflexivity nestačí *)
  Fail rewrite Nat.add_comm. (* a ani rewrite priamo *)
Abort.

(** Pridáme functional extensionality ako axióm *)
Axiom functional_extensionality : 
  forall {X Y : Type} {f g : X -> Y},
    (forall x : X, f x = g x) -> f = g.

(** Teraz môžeme použiť túto axiómu na dôkaz *)
Example function_equality_ex2 :
  (fun x => x + 1) = (fun x => 1 + x).
Proof.
  apply functional_extensionality. intros x.
  apply Nat.add_comm.
Qed.

(** Upozornenie: 
    pridávanie axióm môže byť nebezpečné, 
    pretože môže spôsobiť inkonzistentnosť (možnosť dokázať False). 
    Functional extensionality je však bezpečná axióma. *)

Print Assumptions function_equality_ex2.
(* Axioms:
     functional_extensionality :
       forall (X Y : Type) (f g : X -> Y),
       (forall x : X, f x = g x) -> f = g
*)

(** ----------------------------------------*)
(** -- Vlastnosti aktualizácie zobrazení  --*)

(**
Následujúce vety opisujú základné vlastnosti operácie aktualizácie 
(`update` / `t_update`) nad zobrazeniami (`total_map`, `partial_map`).  

Tieto vlastnosti popisujú, ako sa zobrazenie správa pri:
- vyhľadávaní po aktualizácii,
- aktualizácii rôznych alebo rovnakých kľúčov,
- porovnávaní poradia aktualizácií,
- a pri zachovaní zahrnutia medzi mapami.

Ide o fundamentálne pravidlá, ktoré zaručujú 
konzistentné správanie zobrazení a uľahčujú 
formálne dôkazy o korektnosti programov či stavov v pamäti.
*)

(*------------------------------------------------*)
(** -- Aktualizácia a vyhľadávanie v zobrazení -- *)
(**
Ak aktualizujeme zobrazenie [m] na kľúči [x] novou hodnotou [v] 
a potom vyhľadáme hodnotu na kľúči [x] v novom zobrazení, 
dostaneme späť [v]:

  update m x v x = v

Pre total_map sa hodnota vráti priamo, 
pre partial_map sa vráti Some v.
*)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
intros.
unfold t_update. 
rewrite String.eqb_refl. 
reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

(*------------------------------------------------*)
(** -- Aktualizácia a vyhľadávanie v zobrazení -- *)
(**
Ak aktualizujeme zobrazenie [m] na kľúči [x1] novou hodnotou [v] 
a potom vyhľadáme hodnotu na inom kľúči [x2] (kde x1 <> x2), 
dostaneme rovnaký výsledok, aký by poskytlo pôvodné zobrazenie [m]:

  update m x1 v x2 = m x2
*)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
intros.
unfold t_update.
(* premeniť (x1 =? x2) na false *)
assert (x1 =? x2 = false) as E.
{ apply String.eqb_neq. apply H. }
rewrite E. reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

(*-------------------------------------------------------------*)
(** -- Zahrnutie partial_map a zachovanie pri aktualizácii: -- *)
(**
Pre partial_map zavádzame pojem zahrnutia zobrazení, 
ktorý hovorí, že všetky položky jedného zobrazenia
sú prítomné aj v novom - aktualizovanom zobrazení:

   includedin m m' :=
    forall x v, m x = Some v -> m' x = Some v

Veta [includedin_update] hovorí, že update zachováva zahrnutie:

Ak je [m] zahrnutá v [m'] a aktualizujeme obe zobrazenia na tom istom
kľúči [x] novou hodnotou [vx], potom aktualizované zobrazenie

  [x |-> vx ; m] je zahrnuté v [x |-> vx ; m']:
     includedin m m' ->
        includedin (x |-> vx ; m) (x |-> vx ; m')

Táto vlastnosť je dôležitá pre zachovanie konzistencie a vzťahu
medzi partial_map pri modifikáciách.
 *)


Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : 
forall (A : Type) (m m' : partial_map A) (x : string) (vx : A),
includedin m m' ->
includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
unfold includedin.
intros A m m' x vx H.
intros y vy.
destruct (eqb_spec x y) as [Hxy | Hxy].
- rewrite Hxy.
  rewrite update_eq. rewrite update_eq. intro H1. apply H1.
- rewrite update_neq.
  + rewrite update_neq.
    * apply H.
    * apply Hxy.
  + apply Hxy.
Qed.

(*-------------------------------------------------*)
(** Prekrytie kľúča pri aktualizácii zobrazenia 
    existujúcim kľúčom                          -- *)

(**
Ak aktualizujeme zobrazenie [m] na tom istom kľúči [x] 
dvakrát po sebe s rôznymi hodnotami [v1] a [v2], 
výsledné zobrazenie je rovnaká, ako keby sme aktualizovali 
len poslednou hodnotou [v2]:

  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m)
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m)

Táto vlastnosť sa nazýva "prekrytie" (z ang. shadowing).

Zjednodušene:
Nová aktualizácia na tom istom kľúči prepisuje predchádzajúcu.
*)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
intros.
apply functional_extensionality. 
intro.
unfold t_update. 
destruct (String.eqb_spec x x0) as [H | H]; reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
intros A m x v1 v2. unfold update. rewrite t_update_shadow.
reflexivity.
Qed.

(*------------------------------------------------*)
(** -- Poradie aktualizácií na rôznych kľúčoch -- *)
(**
Ak aktualizujeme zobrazenie [m] na dvoch rôznych kľúčoch [x1] a [x2],
nezáleží na poradí, v akom aktualizácie vykonáme. 
Výsledné zobrazenie sa správa rovnako:

  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m)

*)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
intros.
unfold t_update. 
apply functional_extensionality. intros.
destruct (String.eqb_spec x1 x) as [H1 | H2]. 
- rewrite <- H1. subst. 
  assert (x2 =? x = false) as E.
  { apply String.eqb_neq. apply H. } rewrite E. reflexivity.
- reflexivity. 
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

End maps.

(*============================================*)
(** 2. časť:                                 **)
(** Jednoducho typovaný lambda kalkul s Bool **)
(*============================================*)

(* ################################################ *)
(** * STLC Syntax
  Termy:
       t ::= x                      (premenná)
           | \x:T,t                 (λ-abstrakcia)
           | t t                    (aplikácia)
           | true                   (konštanta true)
           | false                  (konštanta false)
           | if t then t else t     (podmienený výraz)
  Typy:
        T ::= Bool | T -> T
  
  - T -> T - typový konštruktor funkčného typu.
  - Zvolíme jeden základný typ Bool 
    a jednu opéráciu na ňom a to podmienený výraz.
*)

(** Príklady termov:
  Identická funkcia na type Bool:
    [\x:Bool, x]              
    λx:Bool.x

  Identická funkcia aplikovaná na hodnotu true:
    [(\x:Bool, x) true]       
    (λx:Bool.x) true

  Boolean funkcia negácie (not).
    [\x:Bool, if x then false else true]
    λx:Bool. if x then false else true

  Konštantná funkcia, ktorá vráti hodnotu true 
  pre každý vstup:
    [\x:Bool, true]
    λx:Bool.true
*)

(* ################################################ *)
(** * Syntax *)

(** Formalizujeme syntax STLC. *)

Module STLC.

(* ================================================ *)
(** ** Typy *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================ *)
(** ** Termy *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

(** Zavedieme podporu konkrétnej syntaxe 
    prostredníctvom príkazu Notation *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

(** Notácia pre Typy *)
Notation "x" := 
    x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := 
    x (x custom stlc_ty).

Notation "( t )" := 
    t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := 
    (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := 
    t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "'Bool'" := 
    Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.

(** Typy budeme uvádzať [<{{ ... }}>] zátvorkach: *)
Check <{{ Bool }}>.
Check <{{ Bool -> Bool }}>.
Check <{{ (Bool -> Bool) -> Bool }}>.


(** Notácia pre Termy *)
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

Notation "$( x )" := x
     (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := 
    x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := 
    e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := 
    x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := 
    (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
    (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
(** Hint Unfold - 
    Rocq pri dôkazoch bude automaticky 
    rozbaľovať definíciu. 
*)

(** Zhrnutie: 
  - Termy jazyka STLC zapisujeme v: [<{ .. }>] 
  - Typy jazyka STLC zapisujeme v: [<{{ .. }}>].

  [$(..)] Pre návrat do štandardnej Rocq notácie.
 *)

(** Príklady: *)

Notation idB :=
  <{ \x:Bool, x }>.

Notation idBB :=
  <{ \x:Bool->Bool, x }>.

Notation idBBBB :=
  <{ \x: (Bool->Bool)->(Bool->Bool), x}>.

Notation k := 
    <{ \x:Bool, \y:Bool, x }>.

Notation notB := 
    <{ \x:Bool, if x then false else true }>.

(** Poznámka: 
      Používame [Notation] namiesto [Definition] 
      kvôli taktike [auto]. 
*)

(* ################################################ *)
(** * Štrukturálna Operačná Sémantika *)

(** Postup:
  1. Hodnoty v jazyku
  2. Voľné premenná
  3. Substitúcia
  4. Sémantika malých krokov.
*)

(* ################################################ *)
(** === Hodnoty === *)

(**  Hodnoty v našom jazyku môžu byť:
      - konštanty [true] a [false].
      - [\x:T, t] - abstrakcia
*)
Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value <{\x:T, t}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

(** Úplný program:

Intuitívne, „úplný program“ nesmie 
obsahovať nedefinované premenné.

Taký program nazývame uzavretý — 
teda bez voľných premenných.

Naopak, program s voľnými premennými je otvorený term. 

Keďže sme sa rozhodli neredukovať vo vnútri 
abstrakcií, nemusíme riešiť, či sú premenné hodnotami. 
Redukujeme totiž zvonku dovnútra, a teda vždy pracujeme
s uzavretými termami. 
*)

(* ################################################ *)

(**  Substitúcia 

[x:=s]x          = s
[x:=s]y          = y                     ak x <> y
[x:=s](\x:T, t)  = \x:T, t
[x:=s](\y:T, t)  = \y:T, [x:=s]t         ak x <> y
[x:=s](t1 t2)    = ([x:=s]t1) ([x:=s]t2)
[x:=s]true       = true
[x:=s]false      = false
[x:=s](if t1 then t2 else t3) =
      if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)

Reserved Notation "'[' x ':=' s ']' t" 
    (in custom stlc_tm at level 5, x global, 
    s custom stlc_tm, t custom stlc_tm at next level, 
    right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := 
    (subst x s t) (in custom stlc_tm).


(* ################################################ *)
(** Vyhodnocovacie pravidlá:

          value v2
--------------------------- (ST_AppAbs)
(\x:T2,t1) v2 --> [x:=v2]t1

   t1 --> t1'
---------------- (ST_App1)
t1 t2 --> t1' t2

value v1    t2 --> t2'
---------------------- (ST_App2)
  v1 t2 --> v1 t2'
  
-------------------------------- (ST_IfTrue)
(if true then t1 else t2) --> t1

--------------------------------- (ST_IfFalse)
(if false then t1 else t2) --> t2

                     t1 --> t1'
----------------------------------------------------- (ST_If)
(if t1 then t2 else t3) --> (if t1' then t2 else t3)
*)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{[x:=v2]t1}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.
(** Hint Constructors <názov> : <databáza>.
    hovorí systému, aby automaticky používal 
    všetky konštruktory danej induktívnej definície 
    v taktikách ako auto, eauto či trivial.
 *)

Inductive multistep : tm -> tm -> Prop :=
  | multi_refl : forall t, multistep t t  
  | multi_tran : forall t1 t2 t3,
      step t1 t2 ->  
      multistep t2 t3 ->
      multistep t1 t3.
Hint Constructors multistep : core.

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* ################################################ *)
(**  Príklady: *)

Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  apply multi_tran with idB.
  - apply ST_AppAbs.  apply v_abs.
  - simpl. apply multi_refl.  
Qed.

Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof.
  apply multi_tran with 
  (t2:= <{  ((\ x : Bool -> Bool, x) (\ x : Bool, x)) }> ).
  - apply ST_App2.
    + apply v_abs.
    + apply ST_AppAbs. auto.
  - eapply multi_tran.
    + apply ST_AppAbs. simpl. auto.
    + simpl. apply multi_refl.  
Qed.

Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof.
  eapply multi_tran.
  - apply ST_App1. apply ST_AppAbs. auto.
  - simpl. eapply multi_tran.
    + apply ST_AppAbs. auto.
    + simpl. eapply multi_tran.
      * apply ST_IfTrue.
      * apply multi_refl.  
Qed.

Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof.
  eapply multi_tran.
  - apply ST_App2; auto.
  - eapply multi_tran.
    + apply ST_App2; auto.
      apply ST_IfTrue.
    + eapply multi_tran.
      * apply ST_AppAbs. auto.
      * simpl. apply multi_refl.  
Qed.

(* ################################################ *)
(** * Typový systém *)

(* ================================================ *)
(** ** Kontext *)

(**
Hoci nás primárne zaujíma binárna relácia 
          [|-- t \in T], 
ktorá spája uzavretý termín [t] s jeho typom [T],
musíme ju trochu zovšeobecniť.

Pri kontrole, že [\x:T11,t12] má typ [T11->T12], 
potrebujeme overiť, že [t12] má typ [T12]. 
Keďže aplikáciou pravidla pre abstrakciu 
sa odstráni binder [\x], 
potom [x] sa môže vyskytovať voľne v [t12]. 

Pri kontrole typu [t12] je potrebné pamätať, 
že [x] má typ [T11]. 

Podobne, [t12] môže obsahovať ďalšie abstrakcie, 
a overovanie ich tela si môže vyžadovať zistenie typov 
ďalších voľných premenných.

Do relácie pridávame tretí prvok,
typový kontext [Gamma], ktorý uchováva typy premenných, 
ktoré sa môžu voľne vyskytovať v termíne – Gamma.

Kontext Gamma budeme modelovať prostredníctvom 
čiastočného zobrazenia premenných na typy.

Nová typová relácia: [Gamma |-- t \in T] 
a neformálne čítame: term [t] má typ [T], 
vzhľadom na typy voľných premenných v [t] v [Gamma].
*)


(* ================================================ *)
(** ** Čiastočné zobrazenia pre typový kontext      *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := 
        (t_update m x v)
        (at level 100, x constr, right associativity).

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

Definition context := partial_map ty.


(**
Zápis [x |-> T ; Gamma] znamená: 
aktualizácia čiastočného zobrazenia [Gamma] tak, 
aby sa x zobrazovalo na T.
*)

(* ================================================ *)
(** ** Typová relácia *)

(**
Gamma x = T1
------------------ (T_Var)
Gamma |-- x \in T1


x |-> T2 ; Gamma |-- t1 \in T1
------------------------------ (T_Abs)
Gamma |-- \x:T2,t1 \in T2->T1


Gamma |-- t1 \in T2->T1     
Gamma |-- t2 \in T2
--------------------------------- (T_App)
Gamma |-- t1 t2 \in T1


-----------------------  (T_True)
Gamma |-- true \in Bool


------------------------ (T_False)
Gamma |-- false \in Bool


Gamma |-- t1 \in Bool    
Gamma |-- t2 \in T1    
Gamma |-- t3 \in T1
--------------------------------------- (T_If)
Gamma |-- if t1 then t2 else t3 \in T1
*)
  

(** Pri formálnej definícii nižšie
    bude využitá notácia [<{ .. }>] 
*)

Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, 
  v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
(in custom stlc_tm at level 0, x constr at level 0, 
v custom stlc_ty) : stlc_scope.

Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
(at level 0, Gamma custom stlc_tm at level 200, 
t custom stlc_tm, T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
       <{ Gamma |-- t1 \in Bool }> ->
       <{ Gamma |-- t2 \in T1 }> ->
       <{ Gamma |-- t3 \in T1 }> ->
       <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := 
  (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.


(* ================================================ *)
(** ** Príklady: *)

Example typing_example_1 :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. eauto. Qed.

(** Poznámka: 
Keďže sme pridali konštruktory [has_type] do databázy hintov,
taktika [auto] dokáže tento cieľ vyriešiť okamžite. *)

Example typing_example_1' :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. auto. Qed.


Example typing_example_2 :
  <{ empty |-- \x:Bool, \y:Bool->Bool,
          (y (y x)) \in Bool -> (Bool -> Bool) -> Bool }>.
Proof. 
  apply T_Abs. 
  apply T_Abs. 
  apply T_App with (T2 := <{{ Bool }}>).
  - apply T_Var. reflexivity.
  - eapply T_App.
    * apply T_Var. reflexivity.
    * apply T_Var. reflexivity.
Qed.

Example typing_nonexample_1 :
  ~ exists T,
    <{  empty |--
        \x:Bool,
            \y:Bool,
               (x y) \in
        T }>. 
Proof.
  intros Hc. destruct Hc as [T Hc].
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2.
  discriminate H1.
Qed.

End STLC.

