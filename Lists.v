(** * Списки: Работа со Структурированными Данными *)

Require Export Induction.
Module NatList.

(* ###################################################### *)
(** * Пары Чисел *)

(** В определении типа [Inductive], каждый конструктор может принимать 
    любое число аргументов -- ниодного (как в случае [true] и [O]), один (как
    в случае [S]), или больше одного, как в данном примере: *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(** Данное определение может быть прочтено как: "Существует лишь
    один способ построить пару чисел (pair): применяя конструктор [pair]
    ко двум аргументам типа [nat]." *)

Check (pair 3 5).

(** Приведем две простые функция для выделения первой и второй компонент
    пары. Данные определения также иллюстрируют как делается сопостовление
    с образцом на конструкторах от двух аргументов. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Так как пары используются достаточно часто, было бы хорошо уметь
    записывать их используя стандартную математическую нотацию [(x,y)] вместо
    [pair x y].  Мы можем указать Coq разрешить на это с помощью
    декларации [Notation]. *)

Notation "( x , y )" := (pair x y).

(** Новая нотация может быть использована как в выражениях, так и 
    в сопоставлении с образцом (действительно, как мы уже видели это
    в предыдущей части -- такой подход работает так как нотация пары 
    на самом деле, является частью стандартной библиотеки): *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Попробуем доказать несколько простых фактов о парах.

    Если мы будем формулировать факты в некотором определенном (но слегка
    странном) стиле, мы сможем завершать доказательства используя лишь
    reflexivity (и встроенное в нее упрощение): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** Но [reflexivity] неодстаточно, если мы сформулируем лемму в
    ее более естественном виде: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Не упрощается ни к чему! *)
Abort.

(** Нам надо раскрыть структуру [p] так чтобы [simpl] могло
    делать сопостовление с образцом в [fst] и [snd]. Мы можем
    сделать это с помощью [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** Обратите внимание, в отличие от своего поведения на [nat]s, [destruct]
    не генерирует дополнительной подцели здесь. Это следует из того, что 
    [natprod]ы могут быть сконструированы лишь одним способом. *)

(** **** Упражнение: 1 звездочка (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 1 звездочка, дополнительное (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Списки чисел *)

(** Обобщая определения пар, мы можем описать тип _списков_ чисел
    как : "Список либо пустой список, либо является парой из числа и другого
    списка." *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(** Например, вот трехэлементный список: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Как и в случае пар, более удобно записывать списки в знакомой
    нотации, как привычно в программировании. Следующая декларация
    позволяет нам использовать [::] как инфикс [cons] оператор и квадратные
    скобки, как "аутфикс" нотацию для построения списков. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Нет нужды понимать все детали данных определений, но в случае
    если вам интересно, вот что примерно происходит. Аннотация [right associativity]
    указывает Coq как расставлять скобки для выражений использующих
    несколько [::], так чтобы, например, следующие три декларации имели
    в точности один и тот же смысл: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** Часть [at level 60] указывает Coq как раставлять скобки в выражениях
    включающих в себя как [::], так и некоторые другие инфиксные операторы.
    Например, так как мы определили инфиксную нотацию [+] для функции [plus]
    как at level 50 (50й уровень),

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

   то оператор [+] будет связывать теснее чем [::], и [1 + 2 :: [3]]
   будет означать, как мы и ожидали бы, [(1 + 2) :: [3]] вместо [1
   + (2 :: [3])].

   (Выражения вроде "[1 + 2 :: [3]]" могут быть слегка сбиважщими с толку,
   когда читаешь их в .v файле.  Внутренние скобки вокруг 3, указывают на
   список, но внешние скобки, которые не видны в HTML отображении,
   просто инструктируют утилиту "coqdoc" чтобы часть в скобках была
   показана как код Coq, а не простой текст.)

   Вторая и третья декларации [Notation] сверху вводят для списков стандартную
   нотацию с квадратными скобками; правая часть третьей иллюстрирует
   синтаксис Coq для определения н-арной нотации и транслирования
   вложенных последовательностей бинарных конструкторов. *)

(** *** Повтор *)

(** Некоторые функции весьма полезны для манипулирования списками.
    Например, функция [repeat] берет число [n] и счет [count], а возвращает
    список длины [count], где каждый элемент [n]. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** *** Длина *)

(** Функция [length] вычисляет длину списка. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** *** Добавление *)

(** Функция [app] производит конкатенацию (append) двух списков. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** На самом деле, [app] будет часто использовано в некоторых местах
    того, что последует. Поэтому удобно ввести для нее инфиксный оператор. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(** *** Голова (со значением по умолчанию) и Хвост *)

(** Приведем два маленьких примера программирования со списками.
    Функция [hd] возвращает первый элемент ("head" голова) списка,
    в то время как [tl] возвращает все кроме первого элемента
    ("tail" хвост). Конечно, если список пустой, то первого элемента нет,
    так что нам неонходимо передать некоторое значение по умолчанию.  *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(** *** Упражнения *)

(** **** Упражнение: 2 звездочки, рекомендовано (list_funs)  *)
(** Завершите определения [nonzeros] (без нулей), [oddmembers] (нечетные члены) и
    [countoddmembers] (число нечетных членоб) внизу. Взгляните на тесты, чтобы понять
    что данные функции должны делать. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звездочки, продвинутое (alternate)  *)
(** Завершите определение [alternate], которая "зипует" два списка
    в один, чередуя между элементами взятыми из первого списка
    и элементами второго. Взгляните на тесты внизу для более
    конкретных примеров.

    Замечание: один естественный и элегантный способ записать [alternate] 
    не пройдет через требование Coq того чтобы все определения [Fixpoint]
    были бы "очевидно завершающимися."  Если вы обнаружите себя в такой
    ситуации, подумайте о слегка более громоздком решении, которое
    рассматривает элементы обоих списков одновременно. (Одно возможное решение
    требует определения нового вида пар, но это не единственный подход.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ###################################################### *)
(** *** Мультимножества через Списки Lists *)

(** Мультмножество ([bag] или [multiset]) похоже на множество во всем
    за исключением того, что каждый элемент может появлятся в нем
    несколько раз вместо одного. Одна возможная реализация мультимножества
    заключается в представлении его списком. *)

Definition bag := natlist.

(** **** Упражнение: 3 звездочки, рекоммендовано (bag_functions)  *)
(** Завершите следующие определения для функций
    [count] (посчитать число для элемента), [sum] (сумма), [add] (добавить), 
    и [member] (членство) для мультмножеств. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

(** Все данные доказательства могут быть получен одним лишь [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** [sum] для мультмножетсва аналогично [объединению] для множеств: 
    [sum a b] содержит в себе все элементы [a], а также все элементы [b].
    (Математики обычно определяют [объединение] на мультимножествах слегка
    иначе, поэтому мы не используем этот термин для данной операции.)
    Для [sum] мы предоставляем вам заголовок, который не задает явно имен
    аргументов. Более того, он использует ключевое слово
    [Definition] вместо [Fixpoint], так что если бы у вас и были бы
    имена аргументов, вы бы не смогли работать с ними реккурсивно.
    Мы формулируем задачу таким образом, чтобы дать вам возможность
    подумать как и если [sum] может быть определена другим способом --
    возможмно через функии уже определенные вами.  *)

Definition sum : bag -> bag -> bag :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Definition add (v:nat) (s:bag) : bag :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Definition member (v:nat) (s:bag) : bool :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_member1:             member 1 [1;4;1] = true.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звездочки, дополнительное (bag_more_functions)  *)
(** вот несколько дополнительных функций на мультимножествах для практики. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* Когда remove_one применена к мультимножеству без элемента для удаления
     то она должна вернуть тоже мультимножество без изменений. *)
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) admit.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) admit.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) admit.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звездочки, рекоммендовано (bag_theorem)  *)
(** Запишите интеерсную теорему [bag_theorem] о мультимножествах
    включающую в себя функции [count] и [add], и докажите ее. 
    Для этого, замените команду [admit] внизу на утверждение вашей 
    теоремы. Обратите внимание, так как данная задача слегка 
    неопределенная, то вы можете прийти к теореме утверждение которой
    справедливо, но доказательтво которой требует техник, что
    будут предоставлены лишь позднее. Поэтому сбело просите о
    помощи, если застряли! *)

Theorem bag_theorem :
  (* FILL IN HERE *) admit.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Вывод для Списков *)

(** Как и в случае чисел, простые факты о функциях оперирующих на списках
    могут быть доказаны одним лишь упрощением. Например, упрощение
    произведенное с помощью [reflexivity] достаточно для данной
    теоремы... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... так как [[]] подставляется в match определения [app], 
    позволяя упростить по нужной ветке. *)

(** Также как и с числами, иногда полезно проделывать анализ случаев
    на возможных формах (пустой или не пустой) неозвестного списка. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** Здесь, случай [nil] срабатывает так как мы решили определить
    [tl nil = nil]. Обратитите внимание, что аннотация [as] для тактики [destruct]
    здесь вводит два имени, [n] и [l'], соответствующие тому, что
    конструктор для списков [cons] принимает два аргумента (голову и хвост списка, который он
    конструирует). *)

(** Обычно, тем не менее, интересные теоремы о списках требуют
    индукции для своего доказательства. *)

(* ###################################################### *)
(** *** Микро-Напутствие *)

(** Простое чтение примеров скриптов доказательств на заведет вас далеко!
    Важно проработать детали каждого из них, используя Coq и продумывая
    чего достигает каждый шаг. Иначе, более или менее гарантировано, что
    упражнения будут иметь никакого смысла когда вы до них доберетесь. *)

(* ###################################################### *)
(** ** Индукция на Списках *)

(** Доказательства по индукции на структурах данных вроде [natlist] 
    несколько менее привычны, чем стандартная индукция на натуральных
    числах, но идея так же проста.  Каждая декларация [Inductive] 
    определяет множество значений данных, которые можно построить
    используя задекларированные конструктоы: булево значение может быть
    либо [true] либо [false]; число может быть либо [O] или [S] примененное к
    другому числу; список может быть либо [nil] либо [cons] примененный к
    числу и списку.

    Более того, применения задекларированных конструкторов один к
    другому является _единственной_ возможной формой, которую элементы
    индуктивно определенного множества могут иметь. Данный факт
    напрямую задает возможность вывода свойств для индуктивно
    определенных множеств: число есть либо [O] либо иначе [S] примененное
    к некоторому _меньшему_ числу; список есть либо [nil] 
    или иначе [cons] примененный к некоторому числу и некоторому
    _меньшему_ списку; и.т.д. Таким образом, если мы имеем утверждение [P]
    упомянающее список [l] и мы хотим аргументировать, что [P] 
    справедливо для _всех_ списков, мы можем рассуждать следующим образом:

      - Во первых, показать что [P] справедливо для [l] когда [l] есть [nil].

      - Затем показать, что [P] справедливо для [l] когда [l] есть [cons n l']
        для некоторого числа [n] и некоторого меньшего списка [l'], предполагая
        справедливость [P] для [l'].

    Так как большие списки могут быть построены из меньших, в конце достигая [nil],
    данные два аргумента помогают установить справедливость [P] для всех списков [l].
    Приведем конкретный пример: *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Обратите внимание, что как и когда мы делаем индукцию на натуральных числах
    условие [as...] предоставляемое тактике [induction] задает имя индукционной
    гипотезе соответствующей меньшему списку [l1'] случая [cons]. Опять же, данное
    доказательство Coq не является особенно проясняющим все в форме записанного
    документа -- легко увидеть, что происходит, если вы читаете доказательство
    в интерактивной сессии Coq. Тогда вы можете пронаблюдать текущую цель и контекст
    в каждой точке. Все это не видно, в записанном как документ, доказательства Coq.
    Таким образом, доказательство на естественном языке -- записанном для читателей
    людей -- должно включить в себя явные указатели; в частности, читателю будет
    легче ориентироваться, если мы напомним в чем заключается индукционная гипотеза
    во втором случае. *)

(** Для сравнения, вот неформальное доказательство той же самой теоремы. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Доказательство_: По индукции на [l1].

   - Во первых, предположим [l1 = []].  Мы должны показать

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     что следует напрямую из определения [++].

   - Во вторых, предположим [l1 = n::l1'], где

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (индукционная гипотеза). Мы должны показать

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     По определению [++], это следует из

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     что следует напрямую из индукционной гипотезы.  [] *)

(** *** Обращение списка *)

(** Для слегка более продвинутого индуктивного доказательства на списках, предположим
    что мы используем [app] в функцие обращающей список
    [rev]: *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** *** Доказательства об обращении *)

(** Теперь докажем ряд теорем о новоопределенном [rev].
    Для чего то более сложного, чем то что мы уже виделу, докажем
    что обращение списка не меняет его длины. Наша первая попытка
    застревает на втором этапе... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* Это сложный случай. Попробуем как обычно, упрощая. *)
    simpl.
    (* Теперь мы кажется застряли: цель у нас равенство содержащее [++], 
       но у нас нет никаких полезных уравнений ни в непосредственом контексте
       ни в глобальном окружении! Мы можем добиться небольшого прогресс используя
       IH для переписывания цели... *)
    rewrite <- IHl'.
    (* ... но теперь мы уже не можем провинуться дальше. *)
Abort.

(** Возьмем равенство вкльчающее [++] и [length] которое
    позволит нам достичь дальнейшего прогресса и докажем
    его как отдельную лемму. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* СДЕЛАНО В КЛАССЕ *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Обратите внимание на то, что чтобы сделать данную лемму максимально общей
    мы утверждаем для _всех_ [natlist]ов, а не только лишь результатов применения
    [rev]. Это должно быть естественным, ведь правдивость нашей цели не должна
    зависить от того что список обращен. Более того, более общий факт
    легче доказать. *)

(** Теперь мы можем завершить изначальное доказательство. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    rewrite -> IHl'. reflexivity.  Qed.

(** Для сравнения, приведем неформальные доказательстваhere этих двух теорем:

    _Теорема_: Для всех списков [l1] и [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Доказательство_: По индукции на [l1].

    - Во первых, предположим [l1 = []]. Мы должны показать

        length ([] ++ l2) = length [] + length l2,

      что следует напрямую из определений [length] и [++].

    - Далее, предположим [l1 = n::l1'], где

        length (l1' ++ l2) = length l1' + length l2.

      Мы должны показать

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      Это следует напрямую из определений [length], [++]
      и индукционной гипотезы. [] *)

(** _Теорема_: Для всех списков [l], [length (rev l) = length l].

    _Доказательство_: По индукции на [l].

      - Во первых, предположим [l = []]. Нам надо показать

          length (rev []) = length [],

	что следует напрямую из определений [length]
        и [rev].

      - Далее, предположим [l = n::l'], где

          length (rev l') = length l'.

        Мы должны показать

          length (rev (n :: l')) = length (n :: l').

        По определению [rev], это следует из

          length ((rev l') ++ [n]) = S (length l')

        что про предыдущей лемме, тоже самое что и

          length (rev l') + length [n] = S (length l').

	Последнее следует напрямую из индукционной гипотезы и 
        определения [length]. [] *)

(** Такой стиль доказательств довольно длинен и педантичен. После первых несколько
    мы можем прийти к выводу, что следовать доказательствам предоставляющим
    меньше деталей гораздо легче (лишние детали мы всегда можем востановить
    в уме по мере необходимости). Как следствие мы можем лишь выделять
    неочевидные шаги. В таком, более сжатом стиле, предыдущее доказательство
    может выглядеть так: *)

(** _Теорема_:
     Для всех списков [l], [length (rev l) = length l].

    _Доказательство_: Во первых, заметьте что [length (l ++ [n]) = S (length l)]
     для всех списков [l] (это следует из простой индукции по [l]).
     Основное свойство также следует индукцией по [l], используя предыдущее
     наблюдение вместе с индукционной гипотезой для случая [l = n'::l']. [] *)

(** Какой стиль предпочтителен в данной ситуации зависит от степени
    подготовки аудитории и того насколько похоже доказательство
    на те с которыми знакома аудитория. Более педантичный стиль
    будем хорошим по умолчанию для наших текущих целей. *)

(* ###################################################### *)
(** ** [SearchAbout] *)

(** Мы видели, что доказательства могут использовать другие теоремы, 
    из тех что уже доказана, например, используя [rewrite]. Но для того
    чтобы обратиться к теореме нам нужно знать ее имя! Действительно,
    часто довольно трудно помнить какие теоремы были доказаны, не говоря
    уже об их именах.

    Команнда Coq [SearchAbout] бывает полезна для этих случаев. Печатая
    [SearchAbout foo] мы потребуем от Coq показать список всех теорем
    включающих [foo]. Например, попробуйте раскомментировать следующую
    строку, чтобы увидеть список теорем которые мы доказали о [rev]: *)

(*  SearchAbout rev. *)

(** Держите [SearchAbout] в уме когда делаете следующие упражнения, а также
    в дальнейшем работая с книгой; она может спасти вам кучу времени!

    Если вы используете ProofGeneral, вы можете запустить [SearchAbout] с
    помощью [C-c C-a C-a]. Пастнуть ее ответ в ваш буфер вы сможете
    с помощью [C-c C-;]. *)

(* ###################################################### *)
(** ** Упражнения на Списки, Часть 1 *)

(** **** Упражнение: 3 звездочки (list_exercises)  *)
(** Больше практики со списками: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.

(** Существует короткое решение для следующей задачи.  Если вы 
    во время решения запутаетесь, то сделайте шаг назад и поищите
    более простой способ. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.


(** Упражнение на вашу имплементацию функции [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звездочки (beq_natlist)  *)
(** Заполните определение [beq_natlist], которая сравнивает
    списки чисел на равеснтво. Докажите, что [beq_natlist l l]
    выдает [true] для любого списка [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Упражнения на Списки, Часть 2 *)

(** **** Упражнение: 3 звездочки, продвинутое (bag_proofs)  *)
(** Вот несколько маленьких теорем на ваши определения
    связанные с мультимножествами, которые были
    чуть раньше в данном файле. *)

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  (* ЗАПОЛНИТЬ ЗДЕСЪ *) Admitted.

(** Данная лемма о [leb] может помочь вам в следующем доказательстве. *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* ЗАПОЛНИТЬ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звездочки, дополнительное (bag_count_sum)  *)
(** Запишите интересную теорему [bag_count_sum] о мультимножествах
    включающую в себя функции [count] и [sum], и докажите ее.*)

(* ЗАПОЛНИТЕ ЗДЕСЬ *)
(** [] *)

(** **** Упражнение: 4 звездочки, продвинутое (rev_injective)  *)
(** Докажите, что функция [rev] инъективна -- т.е.,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(Есть сложный и простой способы это сделать.) *)

(* ЗАПОЛНИТЕ ЗДЕСЬ *)
(** [] *)


(* ###################################################### *)
(** * Опции *)

(** Преположим, что мы хотим написать функцию, которая возвращает [n]ый
    элемент некоторого списка. Если мы зададим ей тип [nat -> natlist -> nat],
    тогда нам нужно будет выбрать какое либо число для возвращения
    в случае, если список слушком короткий... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* произвольное! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** Это нехорошее решение: Если [nth_bad] возвращает [42], мы не можем
    сказать действительно ли данное значение появляется в списке
    или нет. Более лучшей альтернативой было бы поменять тип
    возвращаемого значения [nth_bad] чтобы включить значение ошибки
    как возможный исход. Мы назовем этот тип [natoption]. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** Тогда мы сможем поменять верхнее определение [nth_bad], чтобы
    оно возвращало [None] когда список слишком короткий и [Some a]
    когда список имеет достаточно членов и [a] находится на позиции [n]. 
    Мы назовем эту новую функцию [nth_error] для индикации того, что
    она может завершаться ошибкой. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** (В версии HTML, шаблонные доказательства данных примеров 
    скрыты. Кликните на вкладыш, если захотите увидеть один.)

    Данный пример также предоставляет возможность ввести еще одну
    возможность языка программирования Coq: условные
    выражения... *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(** Условия Coq в точности такие эе как и те что присутствуют в
    других языках, с одним небольшим обобщением. Так как булев тип не
    является встроенным, Coq на самом деле разрешает условные выражения на
    _любом_ индуктивно определенном типе с ровно двумя конструкторами. 
    Условие считается правдивым, если оно вычисляется в первый конструктор
    [Inductive] определения и неправдивым, когда сводится ко второму. *)

(** Нижняя функция выделяет [nat] из [natoption], возвращая
    предоставленное значение по умолчанию, случае [None]. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Упражнение: 2 звездочки (hd_error)  *)
(** Используя туже идею, поправьте функцию [hd] определенную раннее,
    так чтобы нам не приходилось передавать ей значение по
    умолчанию в случае [nil].  *)

Definition hd_error (l : natlist) : natoption :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example test_hd_error1 : hd_error [] = None.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 1 звездочка, дополнительное (option_elim_hd)  *)
(** Данное упражнение связывает вашу новую [hd_error] со старой [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

End NatList.

(* ###################################################### *)
(** * Частичные Отображения (Partial Maps) *)

(** В качестве последней иллюстрации того как структуры данных могут
    быть определены в Coq, приведем простой тип данных _частичное отображение_,
    аналогичный отображению или структуре данных словаря (dictionary data structures)
    присутствующим в большинстве языков программирования. *)

(** Во первых, определим новый индуктивный тип данных [id] который послужит
    "ключами" для наших частичных отобтажений. *)

Inductive id : Type :=
  | Id : nat -> id.

(** Внутренне, [id] есть просто число. Введение отдельного типа
    упаковывающего каждое nat с пометкой [Id] делает определения более
    читаемыми и предоставляет нам свободу в смене репрезентазии
    если она нам будет нужна в дальнейшем.

    Нам также понадобится тест равенства для [id]: *)

Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Упражнение: 1 звездочка (beq_id_refl)  *)
Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** Теперь мы определим тип частичных отображений: *)

Module PartialMap.
Import NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** Данная декларация моэет быть прочтена как: "Существует два способа
    построить [partial_map]: либо используя конструктор [empty] для 
    представления пустого частичного отображения, либо применяя
    конструктор [record] к ключу, значению и существующему [partial_map]
    для построения [partial_map] с дополнительным отображением ключа-в-значение." *)

(** Функция [update] переписывает запись для данного ключа в частичном 
    отображении (или добавляет новую запись, если заданный ключ отсутствует
    в отображении). *)

Definition update (d : partial_map)
                  (key : id) (value : nat)
                  : partial_map :=
  record key value d.

(** Наконец, функция [find] ищет в [partial_map] заданный ключ. 
    Она возвращает [None] если ключ не найден и [Some val] если
    ключ связан с некоторым [val]. Если тот же ключ связан с 
    несколькими значениями, [find] возвращает первое которое
    встретит. *)

Fixpoint find (key : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record k v d' => if beq_id key k
                     then Some v
                     else find key d'
  end.

(** **** Упражнение: 1 звездочка (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (k : id) (v: nat),
    find k (update d k v) = Some v.
Proof.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 1 star (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (m n : id) (o: nat),
    beq_id m n = false -> find m (update d n o) = find m d.
Proof.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

End PartialMap.

(** **** Упражнение: 2 звездочки (baz_num_elts)  *)
(** Рассмотрите следующее индуктивное определение: *)

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(** Как _много_ элементов имеет тип [baz]?

(* ЗАПОЛНИТЕ ЗДЕСЬ *)
*)
(** [] *)

(** $Date: 2016-05-24 14:00:08 -0400 (Tue, 24 May 2016) $ *)
