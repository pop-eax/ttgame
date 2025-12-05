(**
Prednáška 1: 
- Úvod do funkcionálneho programovania.
- Prvé dôkazy
**)

(*===========================================*)
(**           Základne pojmy                **)
(*===========================================*)

(*
ROCQ (pôvodne COQ) je interaktívny dokazovací systém 
  (proof assistant).
  Pozostáva z viacerých jazykov:
  - Gallina: základný funkcionálny jazyk (teória typov)
  - Vernacular: príkazy - Definition, Inductive, 
                          Lemma, Theorem, Print...
  - Ltack: jazyk - taktiky pre dokazovanie teorém

Oficiálna stránka a dokumentácia:
https://rocq-prover.org/ 
https://rocq-prover.org/docs

Je založený na teórii typov:
Calculus of Inductive Constructions
https://en.wikipedia.org/wiki/Calculus_of_constructions 

Viac informácii na stránke predmetu:
- https://kurzy.kpi.fei.tuke.sk/tt/rocq/01.html 
- Zatiaľ len krátky úvod.
- Konkretnejšie informácie nájdete v komentároch zdrojových kódov.

*)


(*===========================================*)
(**         Organizácia predmetu            **)
(*===========================================*)

(*-------------------------------------------*)
(**               Zápočet                   **)
(*
  Získanie aspoň 21 z 40 bodov za následovné aktivity:
  - Zadanie (30b) pozostáva z 3 odovzdávok po 10b
    v 4. 8. a 12. týždni.
  - Test na cvičení v 13. týždni za 10b.  
  
  V rámci zadania vypracujete úlohy, ktoré nájdete
  predpripravené v zdrojových kódoch k prednáškam.
  
  Úlohy budú pozostávať z špecifikácie
  typov, funkcií a dôkazov. 
  
  Vašou úlohou bude doplniť konkrétne definície a dôkazy.

*)

(*-------------------------------------------*)
(**               Skúška                    **)
(*
  Získanie aspoň 31 z 60 bodov za následovné aktivity:
  - Spoločný test.
  - Teoretická otázka.
  - Príklad.
*)



(*===========================================*)
(**            I. časť                      **)

(*********************************************)
(**  Úvod do funkcionálneho programovania.  **)
(**  - Jazyk Gallina a Vernacular príkazy   **)

(*
Dopytovanie a ovládannie ROCQ prostrednítvom príkazov jazyka Vernacular
- Definícia premenných
- Definícia funkcií
- Informácie o objektoch a vyhľadávanie objektov.
*)

Definition x := 10.

Definition succ (x : nat) : nat := x + 1.

Print x.
Print succ.

Compute (succ x).
Compute (succ 11). 
Compute (1 + 1). (* 2 : nat *)

Check 1.

About plus. 

Print nat.
Print Nat.add.

Search nat.     (* Vráti zoznam hodnôt súvisiacich s nat *)
Search "_ + _". (* Vyhľadávanie podľa vzorov *)
Locate "+".

(*
Definícia funkcií:
- Funkcie vyššieho rádu
- Konštrukcia let
- Pattern matching
*)

Definition plus x y := x + y. 
(* plus je typu nat -> nat -> nat *)

(* Čiastočná aplikácia funkcie *)
Definition plus2 := plus 2.   
(* plus2 je nat -> nat *)
Compute plus2 3. (* Vráti 5 *)

Definition add_xy : nat := let x := 10 in
                           let y := 20 in
                           x + y.

Compute add_xy.

(* Úplne definované funkcie 
    
    V systéme Rocq je možné definovať len úplné funkcie,
    t.j. také, ktoré terminujú pre každý vstup.
    
    Následujúca definícia je validná 
    v jazykoch ako Haskell alebo OCaml,
    ale v Rocq je chybná.

Definition negb (b : bool) :=
    match b with
    | true => false
    end.
*)


(* Rekurzívne funkcie *)
Fixpoint factorial (n:nat) := 
                      match n with
                        | 0 => 1
                        | (S n') => n * factorial n'
                        end.

(* Nepriama rekurzia *)
Fixpoint is_even (n : nat) : bool := match n with
  | 0 => true
  | (S n) => is_odd n
end with
  is_odd n := match n with
  | 0 => false
  | (S n) => is_even n
end.


(*********************************************)
(** Základne typy a hierarchia typov v ROCQ **)

(**
| Typ      | Kde patrí | Význam                      | Príklady hodnôt |
|----------|-----------|-----------------------------|-----------------|
| Set      | Type      | Univerzum dátových typov    | nat, bool, list |
| Prop     | Type      | Univerzum logických tvrdení | True, False, n=0|
| Type     | Type1,2,..| Univerzum všetkých typov    | Set, Prop, list |
| bool     | Set       | Booleovská logika           | true, false     |
| nat      | Set       | Prirodzené čísla (Peano)    | O, S O, S (S O) |
| unit     | Set       | Jeden prvok (triviálny typ) | tt              |
| Empty_set| Set       | Prázdny typ (žiadny prvok)  | --              |
| list A   | Set       | Zoznam prvkov typu A        | nil, cons 1 nil |
**)

Check Set.              (* Set : Type *)
Check Prop.             (* Prop : Type *)
Check Type.             (* Type : Type1 *)

Check bool.             (* bool : Set *)
Check true.             (* true : bool *)
Check false.            (* false : bool *)

Check nat.              (* nat : Set *)
Check O.                (* O : nat *)
Check (S O).            (* S O : nat *)

Check unit.             (* unit : Set *)
Check tt.               (* tt : unit *)

Check Empty_set.        (* Empty_set : Set *)

Check (list).           (* list: Type -> Type *)
Check (list nat).       (* list nat : Set *)
Check (nil : list nat). (* nil : list nat *)
Check (cons 1 nil).     (* cons 1 nil : list nat *)

Check True.             (* True : Prop *)
Check False.            (* False : Prop *)
Check (3 = 4).          (* 3 = 4 : Prop *)
Check (forall n, n + 0 = n).  (* ∀ n, n + 0 = n : Prop *)


(* Anonymne (lambda) funkcie : fun x => x. *)

Definition id_nat : nat -> nat := fun x => x.
Check id_nat.
Print id_nat.

(* To isté ako: *)
Definition id_nat' (x:nat) : nat := x.
Check id_nat'.
Print id_nat'.

(* Polymorfné funkcie *)

Print list.

Definition id_poly (A : Type) (x : A) : A := x.
Definition id_poly2 : forall A : Type, A -> A := fun A x => x.

Compute id_poly nat 3. (* 3 : nat *)

Compute id_poly _ 3.

(* Množinové zátvorky {A : Type} pri paramtre typu 
   definujú jeho odvodenie z druhého argumentu funkcie.
*)

Definition id_poly3 {A : Type} (x : A) : A := x.
Compute id_poly3 3. (* 3 : nat *)

(* Symbolom @ je možné vypnuť automaticé odvodenie typu *)
Compute @ id_poly3 nat 3.
Compute id_poly3 (A:=nat) 3.


(*********************************************)
(**         Vlastné údajové typy            **)

(*
Kľucové slovo Inductive

Definícia:

Inductive TypeName : Type :=
  | Constructor1 : Type1 -> TypeName
  | Constructor2 : Type2 -> TypeName
  | Constructor3 : Type3 -> TypeName
  | ... (* Viac konštruktorov podľa potreby *)
  | ConstructorN : TypeN -> TypeName.


- Konštruktor musí mať jedinečný názov (môže obsahovať parametre).
- Induktívne typy môžu mať aj viaceré parametre. 

Inductive TypeName (param1 : Type1) (param2 : Type2) : Type :=
  | Constructor1 : TypeName param1 param2
  | Constructor2 : ... -> TypeName param1 param2.

*)

Inductive day : Type :=
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday.


Definition next_weekday (d : day) : day :=
  match d with
  | Monday    => Tuesday
  | Tuesday   => Wednesday
  | Wednesday => Thursday
  | Thursday  => Friday
  | Friday    => Saturday
  | Saturday  => Sunday
  | Sunday    => Monday
  end.


(*********************************************)
(**               Moduly                    **)

Module NazovModulu.
Definition foo (n : nat) : nat :=
  n.
End NazovModulu.

(* Prístup k definícii v module z mimo modulu *)
Check NazovModulu.foo.   (* NazovModulu.foo : nat -> nat *)
Eval compute in NazovModulu.foo 5.  (* = 5 : nat *)


(*********************************************)
(**             Notácie                     **)
(*    Rozsahy notácií a príkaz Notation      *)

(*
Coq ma preddefinované nasledujúce rozsahy:

core_scope,
type_scope,
function_scope,
nat_scope,
bool_scope,
list_scope,
int_scope a
uint_scope.

Numerické rozsahy:
- Z_scope (celé čísla) 
- Q_scope (zlomky) 
sú taktiež zahrnuté v moduloch ZArith a QArith.

*)


Compute Nat.add 3 4. (* 7 : nat *)
Compute 3 + 4. (* 7 : nat *)
Print Scope nat_scope.

(* 
   Príklad použitia príkazu Notation 
   nižšie v module NatPlayground 
*)


(*********************************************)
(**          Rekurzívne typy                **)

(* Príklad typ prirodzených čísel *)

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint plus (n: nat) (m: nat) : nat :=
match n with 
| O   => m
| S n => S (plus n m)
end.

Fixpoint mult (n: nat) (m: nat) : nat :=
match n with 
| O   => O
| S n => plus m (mult n m)
end.

Compute (plus (S O) (S O)).
Compute (mult (S(S O)) (S(S O))).

Notation "x * y" := (mult x y)(at level 40, left associativity).
Notation "x + y" := (plus x y)(at level 50, left associativity).
Notation "0"   := (O)(at level 1).
Notation "1"   := (S O)(at level 1).
Notation "2"   := (S 1)(at level 1).
Notation "3"   := (S 2)(at level 1).
Notation "4"   := (S 3)(at level 1).
Notation "5"   := (S 4)(at level 1).
Notation "6"   := (S 5)(at level 1).
Notation "7"   := (S 6)(at level 1).
Notation "8"   := (S 7)(at level 1).
Notation "9"   := (S 8)(at level 1).
Notation "10"   := (S 9)(at level 1).
(* Notácie pre všetky čísla by bolo možné zadefinovať 
   prostredníctvom preprocesorov systému ROCQ, 
   Neskôr budume používať typ zo štandardnej knižnice *)

Compute plus 1 1.
Compute mult 3 2.
Compute mult 3 5. 

Compute 1 + 1.
Compute 3 * 2.
Compute 3 * 5.
 
Compute Nat.add 3 4. 
(* Pouvažujte prečo je výstup iný ako mimo modulu *)

End NatPlayground.  

Compute Nat.add 3 4. 
Print Datatypes.


(*===========================================*)
(**            II. časť                     **)

(*********************************************)
(**             Prvé dôkazy                 **)
(**             Jazyk Ltack                 **)

(* 
   Ltack: Jazyk taktík na konštrukciu dôkazov
   
*)

(*
 Simpl, Reflexivity, Intro(s),
link na documentaciu
*)

(* Ukážky základných taktik v Coq-u *)

(*
  Taktika intro má nepovinné parametre, 
  prostredníctvom ktorých je možné pomenovať
  zavedené objekty v kontexte (predpokladoch) dôkazu.
*)

Theorem refl_nat : forall n : nat, n = n.
Proof.
  intro n.         (* zoberieme ľubovoľné n *)
  reflexivity.     (* triv. rovnosť n = n *)
Qed.


Theorem refl_nat' : forall n : nat, n = n.
Proof.
  intro.         (* zoberieme ľubovoľné n *)
  reflexivity.     (* triv. rovnosť n = n *)
Qed.

Theorem intros : forall (n m : nat),
 n + m = m + n -> n + m = m + n.
Proof.
  intro n.
  intro m.
  intro H.    (* zoberieme n, m a predpoklad H *)
  exact H.         (* použijeme H priamo *)
Qed.


Theorem intros' : forall (n m : nat),
 n + m = m + n -> n + m = m + n.
Proof.
  intros n m H.    (* zoberieme n, m a predpoklad H *)
  exact H.         (* použijeme H priamo *)
Qed.

Theorem dva_plus_tri : 2 + 3 = 5.
Proof.
  simpl.           (* zjednoduší 2 + 3 na 5 *)
  reflexivity.     (* 5 = 5 *)
Qed.

Theorem dva_plus_tri' : 2 + 3 = 5.
Proof.
  reflexivity.     (* 5 = 5 *)
Qed.


Theorem n_plus_0 : forall n, 0 + n = n.
Proof.
  intro n.
  simpl.           (* n + 0 sa zjednoduší na n *)
  reflexivity.     (* n = n *)
Qed.



(*
Proof by rewriting - Rewrite

  rewrite sa používa, keď máme v kontexte rovnosť
  a chceme ju použiť na nahradenie 
  jednej strany rovnice za druhú.
*) 

(* Ukážky dôkazov pomocou rewrite *)

Theorem example_rewrite :
  forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  intros n m H.       (* n, m a predpoklad H: n = m *)
  rewrite H.          (* n nahradíme za m v cieli *)
  reflexivity.        (* m + 1 = m + 1 *)
Qed.

Theorem example_rewrite_backwards :
  forall n m : nat, n = m -> m + 1 = n + 1.
Proof.
  intros n m H.
  rewrite <- H.       (* m nahradíme späť na n *)
  reflexivity.
Qed.

(* Malá lemma, ktorú potom použijeme *)
Theorem plus_O_n : forall n, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem example_rewrite_with_theorem :
  forall n, 0 + n + 1 = n + 1.
Proof.
  intro n.
  rewrite plus_O_n.   (* použijeme lemma plus_O_n *)
  reflexivity.
Qed.

Theorem example_rewrite_chain :
  forall n, n = n + 0 -> n + 1 = (n + 0) + 1.
Proof.
  intros n H.
  rewrite <- H.          (* prepíšeme n na n+0 podľa H *)
  reflexivity.
Qed.


Theorem example_rewrite_chain' :
  forall n, n = n + 0 -> n + 1 = (n + 0) + 1.
Proof.
  intros n H.
  rewrite H.          (* prepíšeme nesprávnym smerom *)
  Admitted.

(*
Kľúčové slovo Admitted.

- Ukončenie neúplného dôkazu.
- Rocq potom prijme výrok ako akoby bol dokázaný,
  avšak je to iba „diera“ v dôkaze.
- Praktické pri vývoji.
*)


(*
Proof by case analysis - Destruct
link na documentaciu

- Taktika destruct sa používa na 
  vykonanie analýzy prípadov bez rekurzie. 
- Taktika generuje podciele pre každý možný konštruktor termu.
- Vhodné pre induktívne typy bez rekurzie.
*)

(* Ukážky dôkazov pomocou destruct *)

Print bool.
(*
    Inductive bool : Set :=  true : bool | false : bool.
*)

Theorem example_destruct_bool :
  forall b : bool, b = b. 
Proof.
  intros b.
  destruct b.      (* rozdelíme na prípady true a false *)
  - reflexivity.   (* prípad true *)
  - reflexivity.   (* prípad false *)
Qed.

Print nat.
(*
    Inductive nat : Set :=  O : nat | S : nat -> nat.
*)

Theorem example_destruct_nat :
  forall n : nat, n = n.
Proof.
  intros n.
  destruct n as [| n'].  (* rozdelíme na O a S n' *)
  - reflexivity.          (* prípad O *)
  - reflexivity.          (* prípad S n' *)
Qed.


