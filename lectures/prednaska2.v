(*
Prednáška 2:
 
- Dôkaz indukciou
- Dôkazy v dôkazoch
- Formálny vs neformálny dôkaz
- Funkcie vyššieho rádu: filter, map, fold
*)

(*
Odporúčam pozrieť prve 2-3 prednášky a pre úvod do dôkazov.
https://ocw.mit.edu/courses/
6-1200j-mathematics-for-computer-science-spring-2024/
video_galleries/lecture-videos/
*)


(* Kniznice pre funkcie nad prirodzenymi cislami,
 dokazy nad Nat a zoznamy *)
Require Import Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

(*===========================================*)
(**               Dôkazy                    **)
(*===========================================*)


(*===========================================*)
(**            Dôkaz indukciou              **)

(* Dôkaz indukciou - Induction *)

(* 
Prípad 1.: Dôkaz indukciou nad prirodzenými číslami: 

Postup dôkazu indukciou pre výrok: 
že nejaké tvrdenie P(n) platí pre všetky n : nat,
je nasledovný:
  1. Základný prípad (base case): ukážeme, že P(0) platí.
  2. Indukčný krok: ukážeme, že ak P(n') platí, tak P(S n') tiež platí.
  3. Záver: z 1. a 2. vyplýva, že P(n) platí pre všetky n.

Formálne je možné princíp dôkazu indukciou vyjadriť formulou:
    (P(0) ∧ ∀n.(P(n) → P(S n))) → ∀n.P(n)

Vychádza zo zákonu modus ponens:
    P   P → Q
   -----------(mp)
        Q

Princíp dôkazu indukciou a modus ponens
- Base case: dokážeme P(0).
- Inductive step: dokážeme ∀n, P(n) → P(S n).
- Indukčná hypotéza: predpokladáme, že P(n') platí pre nejaké n'.
- Modus ponens: z P(n') a P(n') → P(S n') odvodíme P(S n').
- Opakovaním tohto procesu dostaneme P(n) pre všetky n ∈ nat.

    P(0)    P(0) → P(1)
   ---------------------(mp) 
          P(1)

    P(1)    P(1) → P(2)
   ---------------------(mp) 
          P(2)
          
          ...

Zovšeobecnením tohto postupu získame pravidlo:

    P(0)    ∀n.(P(n) → P(n+1)))
   -----------------------------(induction) 
          ∀n. P(n)

Inými slovami,  indukcia je opakovaná aplikácia modus ponens
na postupnosť P(0), P(1), P(2), ...

∀n.(P(n) → P(n+1))) sa nazýva indukčný predpoklad (hypotéza).

Rozdiel medzi taktikami destruct a induction:

- destruct:
  * Používame na analýzu prípadov podľa konštruktorov.
  * Nerozširuje dôkaz o indukčnú hypotézu.
  * Typické pre bool, malé prípady nat, 
    alebo ak stačí rozdeliť na konečný počet možností.

- induction:
  * Používame, keď vlastnosť vyžaduje rekurziu.
  * Okrem rozdelenia na prípady dostaneme aj indukčnú hypotézu.
  * Typické pre dôkazy o nat, list, 
    alebo iných rekurzívnych štruktúrach.
*)

(* Príklad: 0 + n = n vs n + 0 = n *)

Print nat.
(* Inductive nat : Set :=  O : nat | S : nat -> nat. *)

Theorem plus_O_n': forall n:nat, 0 + n = n.
Proof.
intro. simpl. reflexivity.
Qed.


Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
intro. 
(* [| n' IH] nepovinný argument, pomenuje n v dôkaze n' a IH *)
induction n as [| n' IH]. 
- (* Základný prípad: n = 0 *)
  simpl. reflexivity.
- (* Indukčný krok: predpokladajme, že n' + 0 = n' (IH),
     potom dokážeme, že (S n') + 0 = S n' *)
  simpl.
  rewrite IH.
  reflexivity.
Qed.

(*

Základný prípad: n=0
0 + 0 = 0

Indukčný predpoklad:
∀n.(n + 0 = n => P(n+1) = n+1 + 0 = n+1)

Záver:
∀n. P(n) = ∀n.(n + 0 = n)

---------------------------------------------------------------

Princíp predchádzajúceho dôkazu v tvare formuly:

P(0) = 0 + 0 = 0
      /\
∀n.(P(n) => P(n+1)) = ∀n.(n + 0 = n => P(n+1) = n+1 + 0 = n+1)
      => 
Zaver: ∀n. P(n) = ∀n.(n + 0 = n)

---------------------------------------------------------------

V tvare odvodzovacieho pravidla:

    0 + 0 = 0       ∀n.(n + 0 = n => P(n+1) = n+1 + 0 = n+1)
   ---------------------------------------------------------- 
                 ∀n.(n + 0 = n)
*)

(* Dôkaz formuly reprezentujúcej princíp dôkazu indukciou *)

Lemma induction_principle :
  forall (P : nat -> Prop), 
    P 0 ->
    (forall n, P n -> P (S n)) ->
    forall n, P n.
Proof.
  intros P H0 Hstep n.
  induction n as [| n' IH].
  - (* základný prípad *)
    exact H0.
  - (* indukčný krok *)
    apply Hstep.
    exact IH.
Qed.

(*===========================================*)
(**       Dôkazy v dôkazoch                 **)
(*  Taktiky - Exact, Apply, Rewrite, Assert  *)

(*
Taktika exact

- Používame, keď chceme cieľ dokázať presne nejakým predpokladom
  alebo vetou v kontexte.
- Syntax: exact H. kde H : P a cieľ je P.
- exact H povie Rocq-u: 
  „tento predpoklad H presne zodpovedá cieľu, použime ho priamo“.
*)

Theorem identity : forall P : Prop, P -> P.
Proof.
  intros P H.
  exact H.  (* H presne zodpovedá cieľu *)
Qed.

(*
Taktika apply:

- Používame, keď chceme použiť existujúcu vetu 
  alebo predpoklad na dokázanie cieľa.
- Ak máme H : P → Q a cieľ Q, 
  potom apply H použije modus ponens: 
  z P → Q a predpokladu P dostaneme Q.
*)

Theorem modus_ponens :
  forall P Q : Prop,
  P-> (P -> Q) -> Q.
Proof.
  intros P Q H1 H2.
  apply H2.  (* použijeme modus ponens: z P -> Q a P dostaneme Q *)
  exact H1.  (* P je dokázané predpokladom H2 *)
Qed.

(*
Taktika rewrite:

- Používame, keď máme v kontexte rovnosť a chceme ju použiť
  na nahradenie jednej strany rovnice za druhú.
- Syntax: rewrite H. (alebo rewrite <- H. pre opačný smer)
- Po rewrite sa výraz zjednoduší,
  aby sme mohli pokračovať reflexivity alebo ďalšími taktikami.
*)

Theorem rewrite_example :
  forall n : nat, n + 0 = n.
Proof.
  intro n.
  rewrite plus_n_O.  (* použijeme lemmu: n + 0 = n *)
  reflexivity.       (* cieľ je dokázaný *)
Qed.

(*
Taktika "assert (P) as H" alebo "assert (H: P)"

- Vytvorí dva podciele (sub-goals):
  1. Tvrdenie P.
  2. Pôvodný cieľ s predpokladom H : P pridaným do kontextu.

- Používa sa na vloženie medzičlánku dôkazu, 
  ktorý môžeme následne využiť.
- Syntax: assert (n + 0 + 0 = n) as H. Alebo assert (H: P).
- Pre čitateľnosť je možné dôkaz podcieľa 
  uzavrieť do zložených zátvoriek { ... }.
*)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n). 
    { rewrite plus_n_O. rewrite plus_n_O. reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

(* Ďalšie využitie assert a existujúceho dôkazu z knižnice *)


Search "_ + _". 
Check Nat.add_comm.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Je potrebné (n + m) za (m + n)... 
  Dôkaz vety v kniznici Nat.add_comm *)
  rewrite Nat.add_comm.
  (* Nefunguje... Rocq prepíše nesprávne +!*)
Abort.


(*
Použitie lemmy add_comm lokálne

- Ak potrebujeme použiť komutativitu sčítania (add_comm) 
  na konkrétne n a m, môžeme zaviesť "lokálnu vetu" v rámci dôkazu.
- Najprv vytvoríme predpoklad (assert H: n + m = m + n).
- Tento predpoklad dokážeme použitím existujúcej lemmy add_comm.
- Následne môžeme H použiť na prepísanie výrazu 
  (rewrite) a dokončiť dôkaz.
- Takto nemusíme meniť globálny kontext alebo meniť pôvodnú vetu.
*)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite Nat.add_comm. reflexivity. }
  rewrite H. reflexivity. 
Qed.



(*===========================================*)
(**    Formálny vs Neformálny dôkaz         **)

(*
Úvod do formálnych a neformálnych dôkazov

- Formálny dôkaz:
  
  Je napísaný presne podľa logických dedukčných pravidiel.
  Každý krok je možné overiť, takže chyby sú vylúčené.
  
- Neformálny dôkaz:

  Je menej podrobný, často využíva prirodzený jazyk 
  a predpokladá, že čitateľ rozumie základným pravidlám.
  Napríklad indukcia sa opisuje slovami 
  a zjednodušuje sa algebraická manipulácia.

- Výhody:
  * Formálny dôkaz:
    - Istota správnosti.
    - Možnosť overiť korektnosť dôkazu strojom.
    - Presné definície a jednoznačne verifikovateľný celý dôkaz.
  * Neformálny dôkaz:
    - Prehľadnejší a ľahšie čitateľný pre ľudí.
    - Lepšie na intuitívne vysvetlenie myšlienky dôkazu.
  
  Hlavnou výhodou formálneho dôkazu je overiteľnosť počitačom
  čo je zásadné pri matematickej formalizácii 
  a programovaní verifikovaných algoritmov .
*)


(* Príklad neformálny a formálny dôkaz: 

Teoréma: Pre každé prirodzené číslo n platí n + 0 = n.

Dôkaz:

Dôkaz vykonáme indukciou na n.

- Základný prípad: n = 0
  Musíme ukázať:
      0 + 0 = 0
  Toto vyplýva priamo z definície sčítania.

- Indukčný krok: predpokladajme, že n = n' + 1
  a že pre n' platí indukčná hypotéza:
      n' + 0 = n'
  Musíme ukázať:
      (n' + 1) + 0 = n' + 1
  Podľa definície sčítania:
      (n' + 1) + 0 = (n' + 0) + 1
  A z indukčnej hypotézy vieme, že n' + 0 = n', takže:
      (n' + 0) + 1 = n' + 1
  Teda:
      (n' + 1) + 0 = n' + 1
  Čo je presne to, čo sme chceli dokázať.

QED.

----------------------------------------------------------------

Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
intro. 
(* [| n' IH] nepovinný argument, pomenuje n v dôkaze n' a IH *)
induction n as [| n' IH]. 
- (* Základný prípad: n = 0 *)
  simpl. reflexivity.
- (* Indukčný krok: predpokladajme, že n' + 0 = n' (IH),
     potom dokážeme, že (S n') + 0 = S n' *)
  simpl.
  rewrite IH.
  reflexivity.
Qed.

*)


(*===========================================*)
(**         Funkcie vyššieho rádu           **)
(*===========================================*)
(*
Ako väčšina moderných programovacích jazykov – 
najmä funkcionálnych jazykov ako:
OCaml, Haskell, Racket, Scala, Clojure a pod. 
aj Rocq považuje funkcie za "first-class citizens".

To znamená, že funkcie je možné:
  - odovzdávať ako argumenty iným funkciám,
  - vracať ako výsledky,
  - ukladať do údajových štruktúr, atď.

Funkcie vyššieho rádu (Higher-Order Functions) sú funkcie,
ktoré manipulujú s inými funkciami.
*)

(* Jednoduchý príklad:

Definícia funkcie, ktorá aplikuje danú funkciu trikrát:
*)

Definition doit2times {X : Type} (f : X -> X) (n : X) : X :=
  f (f n).

(*
Argument f je funkcia (z X do X), telo funkcie doit2times
aplikuje f dvakrát na hodnotu n.
*)

Check @doit2times.  (* ∀ X : Type, (X → X) → X → X *)

(* 
Príklad použitia:
*)
Definition succ (n:nat):nat := n+1.


Compute doit2times succ 1.

Example test_doit2times: doit2times succ 1 = 3.
Proof. reflexivity. Qed.

(* 
  Ako argument funkcie vyššieho rádu je možné použiť
  aj anonymné funkcie
*)

Compute doit2times (fun x:nat => x+1) 1.

(*===========================================*)
(**               filter                    **)
(*
- Prijíma:
    1. zoznam (list) hodnôt typu X,
    2. predikát na X (funkciu z X do bool),
  Vracia: nový zoznam obsahujúci len tie prvky,
  pre ktoré predikát vráti true.
*)

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | head :: tail =>
      if test head then head :: (filter test tail)
      else filter test tail
  end.

(*
- Príklad použitia:
  Aplikácia filter na predikát 'even' a zoznam čísel l,
  výsledkom bude zoznam obsahujúci len párne elementy zoznamu l.
*)

Compute (filter even [1;2;3;4;5;6]).



(*===========================================*)
(**                map                      **)

(*
Map – ďalšia užitočná funkcia vyššieho rádu

- Funkcia map prijíma:
    1. funkciu f : X → Y,
    2. zoznam l : list X
  a vracia zoznam list Y, 
  kde sa f aplikuje na každý prvok pôvodného zoznamu.
*)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | head :: tail => (f head) :: (map f tail)
  end.

(* Príklad 1: *)
Compute map (fun x => x + 5) [4;0;5;6;9].

(* Príklad 2: *)
Compute map odd [4;0;5;6;9].

(* Príklad 3: *)
Compute map (fun n => [even n; odd n]) [4;0;5;6;9].


(*===========================================*)
(**               fold                      **)

(*
Veľmi často používana funkcia.

- Funkcia fold prijíma:
    1. binárnu funkciu f : X → Y → Y
    2. zoznam l : list X
    3. počiatočnú hodnotu b : Y
  a aplikuje f medzi každé dva prvky zoznamu 
  s využitím b ako počiatočného "akumulátora"
  pričom najčastejšie je to neutrálny prvok danej operácie.
*)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(*
- Intuitívne: fold vloží binárnu operáciu f medzi všetky prvky zoznamu.
  Napr. fold plus [1;2;3;4] 0 = 1 + (2 + (3 + (4 + 0)))
*)

Compute fold plus [1;2;3;4] 0.

Check (fold andb).  (* list bool -> bool -> bool *)

Compute fold andb [true;true;true;true] false.
Compute fold andb [true;true;true;true] true.
Compute fold andb [true;true;false;true] true.

Compute fold mult [1;2;3;4] 1.
Compute fold mult [1;2;3;4] 0.
Compute fold (fun l n => length l + n) [[1];[];[2;3;2];[4]] 0.
Compute fold (fun l acc => l ++ acc) [[1]; [2;3]; [4]] [].


(*
Poznámka o typoch funkcie fold

- Typ funkcie fold je parametrizovaný dvoma typmi, X a Y:
    fold : (X -> Y -> Y) -> list X -> Y -> Y

- Parameter f je binárny operátor, ktorý prijíma hodnotu typu X
  a hodnotu typu Y a vracia hodnotu typu Y.

- Situácia, kde by X a Y boli rôzne:
    - Máme zoznam prvkov typu X (napr. čísla) 
      a chceme akumulovať výsledok
      iného typu Y 
      (napr. zoznam, reťazec, bool, alebo vlastnú štruktúru).
    - Príklad:
       * Zoznam čísel a chceme získať súčet všetkých čísiel
         → X = nat, Y = nat.
       * Zoznam čísel a chceme vytvoriť zoznam bool hodnôt 
         podľa predikátu (napr. párne/ nepárne) → X = nat, Y = list bool.
       * Zoznam reťazcov a chceme spojiť ich dĺžky → X = string, Y = nat.
- Týmto spôsobom fold poskytuje flexibilitu pri práci
  so zoznammi rôznych typov a umožňuje kombinovať alebo 
  transformovať hodnoty do iného typu.
*)