(** * Poly: Полиморфизм и Функции Высшего Порядка *)

(* НАПОМИНАНИЕ: Пожалуйста не выкладывайте решения упражнений
   в публичный доступ. Спасибо! *)

Require Export Lists.

(* ###################################################### *)
(** * Полиморфизм *)

(** В данной главе мы продолжим развитие основных концепций
    функционального программирования. Новыми важными идеями будут
    _полиморфизм_ (абстрагирование функций от типов данных которыми
    они манипулируют) и _функции высшего порядка_ (использование
    функций как данных). Мы начнем с полиморфизма. *)

(* ###################################################### *)
(** ** Полиморфные списки *)

(** В последних разделах мы работали в основном со списками чисел.
    Очевидно, что интересные программы должны иметь возможность
    манипулировать списками из элементов и других типов --
    списками строк, списками булевых значений, списками списков и т.д.
    Мы _могли бы_ просто определить новый индуктивный тип данных для
    каждого случая, например... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... но это может быстро стать утомительным, частично потому что
    нам надо придумывать разные имена каждому новому конструтору,
    но больше потому что нам также придется определять каждый раз
    новые версии всех функций, манипулирующих списками ([length], [rev], и т.д.)
    для каждой нобой структуры данных. *)

(** Чтобы исключить все эти повторения, Coq поддерживает _полиморфные_
    определения индуктивных типов. Например, вот структура данных _полиморфный
    список_. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** Оно точно такое же как определение [natlist] из предыдушей
    главы, за исключением того что аргумент [nat] для конструктора [cons]
    заменен на произвольный тип [X], связывние для [X] добавлено в заголовок,
    и все появления [natlist] в типах конструкторов были заменены на
    [list X].  (Мы можем повторно использовать конструкторы [nil] и [cons]
    потому что ранние определения [natlist] были сделаны внутри определения
    [Module] и теперь вне области видимости.) 

    Что такое [list] сам по себе?  Хороший способ думать о нем как
    о функции [list] из [Type]ов в определения [Inductive]; или, иначе
    ,[list] есть функция из [Type]ов в [Type]ы.  Для любого конкретного типа [X],
    тип [list X] есть индуктивно ([Inductive]) определенное множество списков
    чьи элементы принадлежат типу [X]. *)

(** С данным определением, когда мы используем конструкторы [nil] и
    [cons] для посторения списков, нам нужно указать Coq тип элементов
    в списках, которые мы строим -- т.е, [nil] и [cons] теперь
    _полмирофные конструкторы_. Посмотрите на типы этих конструкторов: *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** (Замечание о нотации: В файлах .v, квантор всеобщности "forall" 
    выписан буквами. В сгенерированных HTML файлах, [forall] обычно
    выписан как обычное "перевернутое А", но бы увидете "forall" в некоторых
    местах, как в комментах наверху. Это просто особенности отображения
    и тут нет разницы в смысле.) *)

(** "[forall X]" в этих типах может быть прочтен как дополнительный аргумент
    конструкторам, который определяет ожидаемые типы аргументов что следуют.
    Когда используются [nil] и [cons], эти аргументы предоставляются так же
    как и остальные. Например, список содержащий [2] и [1] может быть
    записан как: *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** (Мы записали явно [nil] и [cons] здесь, так как мы еще не определили
    нотации [ [] ] и [::] для новой версии определения списков. Мы скоро
    это сделаем.) *)

(** Мы теперь можем вернуться и сделать полиморфные версии всех
    функций работающих со списками, что были определны ранее.  Вот
    например определение [repeat]: *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** Как и в случае [nil] и [cons], мы можем использовать [repeat] применяя ее
    сначало к типу, а затем к аргументу списка: *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(** Чтобы использовать [repeat] для построения списков других видов, мы просто
    подставляем нужный параметер типа: *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.

Module MumbleGrumble.

(** **** Упражнение: 2 звездочки (mumble_grumble)  *)
(** Рассмотрите следующие два индуктивно определенных типа. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Какие из следующих выражений будут типа [grumble X] для
    некоторых [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
(* ЗАПОЛНИТЕ ЗДЕСЬ *)
*)
(** [] *)

End MumbleGrumble.

(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Давайте запишем определение [repeat] снова, но в этот раз мы не
    будем определять типы любых ее аргументов. Примет ли его Coq 
    в этом случае? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** Десйтвительно принимает.  Посмотрим что за тип Coq назначил [repeat']: *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(** Она имеет точно такой же тип как и [repeat].  Coq оказался
    способен использовать _вывод типов_ чтобы узнать каковы должны быть
    типы [X], [x] и [count], основываясь на том, как они использованы. Например,
    так как [X] использован как аргумент для [cons], то он должен быть [Type], 
    так как [cons] ожидает [Type] в качестве своего первого аргумента; сопоставление [count]
    с [0] и [S] означает, что он должен быть [nat]; и так далее.

    Данная мощная функциональность означает, что нам не обязательно
    все время писать явные аннотации типов, хотя явные аннотации
    типов всеже очень полезны как документация и проверка, так что
    мы продолжим их использовать большую часть времени. Вы должны
    постараться найти баланс в своем коде между слишком большим
    числом аннотаций типов (которые загромождают и отвлекают) и
    слишком малым (что заставляет читателя делать вывод типов
    в голове, в попытках понять ваш код). *)

(* ###################################################### *)
(** *** Type Argument Synthesis *)

(** Для использования полиморфной функции, нам необходимо передать
    ей один или более типов дополнительно к ее аргументам. Например,
    реккурсивный вызов в теле функции [repeat] сверху должен передать
    также тип [X].  Но так как второй аргумент [repeat] является элементом [X],
    кажется очевидным, что первым аргументом может быть только [X] -- зачем
    писать его явно?

    К счастью, Coq позовляет обойти такую избыточность. Вместо любого
    аргумента типа мы можем записать "неявный аргумент"
    [_], который может быть прочтен как "Пожалуйста, попробуй сам определить
    что здесь должно быть." Более точно, когда Coq встречает [_], он пробует
    _унифицировать_ (объединить) всю локально доступную информацию -- тип
    применяемой функции, типы других ее аргументов, а также тип ожидаемый
    контекстом в котором применение происходит -- чтобы определить
    какой конкретный тип должен заменить [_].

    Это может звучать похоже на вывод аннотации типов -- действительно,
    обе процедуры основываются на тех же основополагающихся механизмах.
    Вместо простого опускания типов некоторых аргументов функции, как

      repeat' X x count : list X :=

    мы заменяем типы на [_]

      repeat' (X : _) (x : _) (count : _) : list X :=

    чтобы указать Coq на необходимость попытки вывести недостающую информацию.

    Используя неявные аргументы, функция [repeat] может быть записана как: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** В данной весрии мы не сохраняем много места записывая [_] вместо
    [X].  Но во многих случаях разница в обоих нажатиях клавиши и
    читаемости может быть нетривиальной. Например, предположим что мы
    хотим выписать список состоящий из чисел [1], [2], и [3]. Вместо
    записи... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...мы можем использовать синтез аргумента, чтобы написать: *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Неявные Аргументы *)

(** Мы можем зайти дальше и избежать записи [_] в большинстве случаев
    указав Coq _всегда_ выводить тип аргумента(ов) заданной функции.
    Директива [Arguments] задает имя функции (или конструктора), а затем
    список имен ее аргументов, с фигурными скобками вокруг аргументов
    которые будут рассмотрены как неявные.  (Если некоторые аргументы
    определения не имеют имен, как это часто бывает для конструкторов,
    они могут быть указаны в виде [_].) *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** Теперь, нам не нужно предоставлять аргумент типа: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** В качестве альтернативы, мы можем задать аргумент как неявный
    при определении самой функции, заключая его в фигурные скобки.
    Например: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** (Заметьте, что мы не предоставляли аргумент типа в реккурсивном
    вызове [repeat''']; действительно, это было бы даже ошибкой,
    если это делать!)

    Мы будем использовать последний стиль везде где возможно, но
    мы продолжим использовать явные декларации [Argument] для
    конструкторов [Inductive]. Причина по которой мы это делаем, заключается
    в том, что маркируя параметры индуктивного типа как неявные
    заставляет их стать неявными для самого типа, а не только для
    конструкторов. Например, рассмотрим альтернативное определение
    типа [list]: *)

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

(** Так как [X] задан неявно для _всего_ индуктивного определения
    включая сам [list'], мы теперь должны писать только
    [list'] независимо от того говорим ли мы о списках чисел или
    булевых значениях, или о чем то другом, вместо [list' nat] или [list' bool]
    и так далее. Это шаг слишком далеко. *)

(** Давайте закончим переопределять несколько других стандартных
    функций на списках для  наших полиморфных списков... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(** Одна маленькая проблема в задании аргуметов как [Implicit] 
    состоит в том, что иногда, Coq не имеет достаточно локальной информации
    для определения аргумента типа; в таких случаях, нам надо указать Coq
    что мы хотим задать аргумент явно только в этот момент. Например,
    предположим мы написали это: *)

Fail Definition mynil := nil.

(** (Определитель [Fail] который появляется до [Definition] может быть
    использован с _любой_ командой и используется для того чтобы
    быть уверенным, что команда действительно не срабатывает, когда
    вызвана. Если команда не срабатывает, Coq печатает соответствующее
    сообщение ошибки, но продолжает обрабатывать остаток файла.)

    Здесь, Coq сообщает об ошибке, потому что не знает какой 
    аргумент типа предоставить [nil]. Мы можем помочь ему предоставив
    явную декларацию типа (так что у Coq будет больше доступной информации
    когда он дойдет до "применения" [nil]): *)

Definition mynil : list nat := nil.

(** Альтернативно, мы можем заставить неявные аргументы стать явными
    используя префикс [@] перед именем функции. *)

Check @nil.

Definition mynil' := @nil nat.

(** Используя синтез аргументов и неявные аргументы, мы можем определить
    удобные нотации для списков, как и раньше.  Так как мы сделали
    аргументы типа для конструктора неявными, Coq будет автоматически
    выводить их когда мы используем нотации. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Теперь списко могут быть записаны так как нам бы и хотелось: *)

Definition list123''' := [1; 2; 3].

(* ###################################################### *)
(** *** Упражнения *)

(** **** Exercise: 2 stars, optional (poly_exercises)  *)
(** вот несколько простых упражнений, похожих на те что были в главе [Lists],
    для практики с полиморфизмом. Завершите доказательства. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (*ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звездочки, дополнительное (more_poly_exercises)  *)
(** Вот несколько более интересных... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Полиморфные Пары *)

(** Следуя тому же шаблону, определение типа, что мы задали в прошлой
    главе для пары чисел может быть обобщено до
    _полиморфных пар_, часто называемых _произведениями_: *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(** Как и в случае списков, мы делаем аргументы типа неявными и определяем 
    знакомую конкретную нотацию. *)

Notation "( x , y )" := (pair x y).

(** Мы также можем использовать механизм [Notation] для определения стандартной
    нотации для _типов_ произведения: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (Аннотация [: type_scope] указывает Coq на то что данная абревиатура
    должна быть использована только для парсинга типов. Это избегает
    столкновения с символом умножения.) *)

(** Легко в начале путать [(x,y)] и [X*Y]. Помните что
    [(x,y)] есть _значение_ построенное из двух других значений,
    в то время как [X*Y] есть _тип_ построенный из двух других типов.
    Если [x] имеет тип [X] и [y] имеет тип [Y], тогда [(x,y)] имеет тип [X*Y]. *)

(** Фунцкии первой и второй проекции теперь будут выглядеть
    также лал в любом другом функциональном языке программирования. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** Следующая функция берет два списка и объединяет их в список
    пар. В других функциональных языках программирования она часто
    называется [zip]; мы назовем ее [combine] для соответствия со стандартной
    библиотекой Coq. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Упражнение: 1 звездочка, дополнительное (combine_checks)  *)
(** Попробуйте ответить на данные вопросы на бумаге, а затем проверьте
    свои отверы в coq:
    - Какой тип у [combine] (т.е., что печатает [Check
      @combine]?)
    - Что печатает

        Compute (combine [1;2] [false;false;true;true]).

      ?   [] *)

(** **** Упражнение: 2 звездочки, рекоммендованное (split)  *)
(** Функция [split] есть обратная к [combine]: она берет список пар
    и возвращает пару списков. Во многих функциональных языках
    она называется [unzip].

    Расскоментируйте материал внизу и заполните определение
    [split].  Удостоверьтесь, что она проходит заданный юнит тест. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
(* ЗАПОЛНИТЕ ЗДЕСЬ*) admit.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Полиморфные Опции *)

(** Еще один полиморфный тип напоследок: _полиморфные опции_,
    который обощает [natoption] из предыдущей главы: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** Мы теперь можем переписать функцию [nth_error] так чтобы она работала
    с любым типом списков. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** Упражнение: 1 звездочка, дополнительное (hd_error_poly)  *)
(** Завершите определение полиморфной версии функции
    [hd_error] из предыдущей части. Убедитесь, что она проходит
    юнит тесты приведенные внизу. *)

Definition hd_error {X : Type} (l : list X) : option X :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

(** Опять же, чтобы заставить неявные аргументы стать явными
    мы можем использовать [@] перед именем функции. *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Functions as Data *)

(** Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc.*)

(* ###################################################### *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Filter *)

(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Anonymous Functions *)

(** It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

(** Here is the [filter] example, rewritten to use an anonymous
    function. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (filter_even_gt7)  *)
(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  (* FILL IN HERE *) admit.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (partition)  *)
(** Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
(* FILL IN HERE *) admit.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(** *** Exercises *)

(** **** Exercise: 3 stars (map_rev)  *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, recommended (flat_map)  *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].

*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  (* FILL IN HERE *) admit.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 2 stars, optional (implicit_args)  *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)  [] *)

(* ###################################################### *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,

       fold plus [1;2;3;4] 0

    yields

       1 + (2 + (3 + (4 + 0))).

    Some more examples: *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, advanced (fold_types_different)  *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* ###################################################### *)
(** ** Функция Конструирующая Функции *)

(** Большинство функций высшего порядка о которых мы говорили до сих пор
    принимает функции как аргументы. Давайте рассмотрим некоторые примеры
    включающие _возврат_ функций как результат других функций.
    Для начала, вот функция которая берет значение [x] (взятое из некоторого
    типа [X]) и возвращает функцию из [nat] в [X] которая производит
    [x] всегда когда вызвана, игнорируя ее [nat] аргумент. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** На самом деле, функции нескольких аргументов, что мы видели до этого
    также являются примерами передачи функций как данных. Чтобы увидеть
    почему, вспомните тип [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Каждая [->] в выражении есть на самом деле _бинарный_ оператор
    на типах. Этот оператор _право ассоциативен, так что тип 
    [plus] является сокращением для [nat -> (nat -> nat)] -- т.е.,
    он может быть прочтен как "[plus] есть одноаргументная функция
    принимающая [nat] и возвращающая одноаргументную функцию, которая
    принимает другой [nat] и возвращает [nat]."  В примерах сверху, мы всегда
    применяли [plus] к обоим ее аргументам сразу, но если мы хотим, то
    можем предоставить лишь первый. Это называется _частичным применением_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ##################################################### *)
(** * Дополнительные Упражнения *)

Module Exercises.

(** **** Упражнение: 2 звездочки (fold_length)  *)
(** Многие часто применяемые функции на списках могут быть определены в терминах
   [fold].  Например, вот альтернативное определение [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Докажите корректность функции [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звездочки (fold_map)  *)
(** Мы также можем определить [map] в терминах [fold].  Завершите [fold_map]
    внизу. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

(** Запишите теорему [fold_map_correct] в Coq, утверждающую, что
   [fold_map] корректна, и докажите ее. *)

(* ЗАПОЛНИТЕ ЗДЕСЬ *)
(** [] *)

(** **** Упражнение: 2 звездочки, продвинутое (каррирование)  *)
(** В Coq, функция [f : A -> B -> C] на самом деле имеет тип [A
    -> (B -> C)].  т.е., если вы предоставляете [f] значение типа [A],
    то она предоставит вам функцию [f' : B -> C]. Если затем вы предоставите [f']
    значение типа [B], она возвратит значение типа [C]. Это позволяет
    частичное применение, как в [plus3].  Обработка списка аргументов
    функциями, что возвращают функции называется _каррированием_, 
    в честь логика Haskell Curry.

    Обратно, мы можем интерпретировать тип [A -> B -> C] ка [(A *
    B) -> C].  Это называется _декаррированием_. С декаррированной
    бинарной функциек, оба аргумента должны быть предоставлены одновременно
    как пара. В этом случае нет частичного применения. *)

(** Мы можем определить каррирование следующим образом: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** Как упражнение, определите ей обратную [prod_uncurry]. Затем
    докажите теоремы внизу, чтобы показать их обратность. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

(** Как тривиальный пример полезности каррирования, мы можем
    использовать ее для сокращения одного из примеров
    что мы видел раньше: *)

Example test_map2: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** Мысленное упражнение: прежде чем запускать следующие команды,
    можете ли вы расчитать типы [prod_curry] и [prod_uncurry]? *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звездочки, продвинутое (nth_error_informal)  *)
(** Вспомните определение функции [nth_error]:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.

   Запишите неформальное доказательство следующей теоремы:

   forall X n l, length l = n -> @nth_error X l n = None

(* ЗАПОЛНИТЕ ЗДЕСЬ *)
*)
(** [] *)

(** **** Упражнение: 4 звездочки, продвинутое (church_numerals)  *)
(** Данное упражнение исследует альтернативный способ определения
    натуральных чисел, используя, так называемые _нумералы Черча_,
    названные в честь математика Alonzo Church. Мы можем представить
    натуральное число [n] как функцию которая принимает функцию [f] 
    в качестве параметра и возвращает [f] итеррированную [n] раз. *)

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Давайте посмотрим как записать некоторые числа в данной нотации.
    Одна итерация функции естъ тоже самое, что ее применение. Таким
    образом: *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Таким же образом, [two] должно дважды применить [f] к своему аргументу: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Определить [zero] (нуль) несколько труднее: как можно "применить функцию
    нуль раз"?  Ответ на самом деле прост: простон возвратить аргумент как есть. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** Обобщая, число [n] может быть записано как [fun X f x => f (f
    ... (f x) ...)], с [n] записями [f]. Заметьте в частности,
    что функция [doit3times], которую мы определили ранее, есть
    на самом делел просто репрезентация Черча для [3]. *)

Definition three : nat := @doit3times.

(** Завершите определение следующих функций. Убедитесь
    что соответствующие юнит тесты проходят, доказывая их с
    помощью [reflexivity]. *)

(** Следующее за данным натуральное число: *)

Definition succ (n : nat) : nat :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example succ_1 : succ zero = one.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example succ_2 : succ one = two.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example succ_3 : succ two = three.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Сложение двух натуральных чисел: *)

Definition plus (n m : nat) : nat :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example plus_1 : plus zero one = one.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Умножение: *)

Definition mult (n m : nat) : nat :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example mult_1 : mult one one = one.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Возведение в степень: *)

(** (_Подсказка_: Полиморфизм играет критически важную роль здесь.
    Тем не менее выбор правильного типа для итерации может быть
    не простым. Если вы столкнетесь с ошибкой "Universe inconsistency",
    попробуйте итерировать по другому типу: [nat] сам по себе обычно
    проблематичен.) *)

Definition exp (n m : nat) : nat :=
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) admit.

Example exp_1 : exp two two = plus two two.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

End Church.
(** [] *)

End Exercises.

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)

