(ns propel.core
  (:gen-class))

(def example-push-state
  {:exec '()
   :integer '(1 2 3 4 5 6 7)
   :string '("abc")
   :input {:in1 41}})

; Instructions must all be either functions that take one Push state and return another
; or constant literals.
; TMH: ERCs?
(def default-instructions
  (list
   'integer_+;;Think about removing integer operations
   'integer_-
   'integer_*
   'integer_%
   'integer_=
   'integer_<
   'integer_
   'exec_dup
   'exec_if
   'boolean_and
   'boolean_or
   'boolean_not
   'boolean_=
   'close
   ;;Sort Instructions
   'element_swap
   'element_at
   'element_last
   'element_all
   0
   1
   true
   false))

(def sort-instructions
  (list
   'integer_%
   'integer_=
   'integer_<
   'integer_>
   'exec_dup
   'exec_if
   'boolean_and
   'boolean_or
   'boolean_not
   'boolean_=
   'close
   ;;Sort Instructions
   'element_swap
   'element_at
   'element_first
   'element_last
   'element_all
   true
   false))

(def opens ; number of blocks opened by instructions (default = 0)
  {'exec_dup 1
   'exec_if 2})

;;;;;;;;;
;; Utilities

(def empty-push-state
  {:exec '()
   :integer '()
   :boolean '()
   :swap-count 0
   :input []})

(defn abs
  "Absolute value."
  [x]
  (if (neg? x)
    (- x)
    x))

(defn swap
  "Swaps elements at index i1 and i2 in vector v
   From: https://stackoverflow.com/questions/5979538/what-is-the-idiomatic-way-to-swap-two-elements-in-a-vector"
  [v i1 i2]
  ;(println "I1:" i1)
  ;(println "I2:" i2)
  (assoc v i2 (v i1) i1 (v i2)))

(defn pareto-dominant?
  "Returns true if indv1 partially dominates indv2"
  [indv1 indv2]
  (if (and (< (:swaps indv1) (:swaps indv2))
          (< (:total-error indv1) (:total-error indv2)))
    true
    false))

(defn on-pareto-front?
  "Returns true if indv dominates at least one other indv in pop"
  [indv pop]
  (if (some #(pareto-dominant? %1 indv) pop)
    true
    false))

(defn not-lazy
  "Returns lst if it is not a list, or a non-lazy version of lst if it is."
  [lst]
  (if (seq? lst)
    (apply list lst)
    lst))

(defn not-lazy-vector
  [lst]
  (if (seq? lst)
    (apply vector lst)
    lst))

(defn push-to-stack
  "Pushes item onto stack in state"
  [state stack item]
  (update state stack conj item))

(defn pop-stack
  "Removes top item of stack."
  [state stack]
  (update state stack rest))

(defn peek-stack
  "Returns top item on a stack."
  [state stack]
  (if (empty? (get state stack))
    :no-stack-item
    (first (get state stack))))

(defn empty-stack?
  "Returns true if the stack is empty."
  [state stack]
  (empty? (get state stack)))

(defn get-args-from-stacks
  "Takes a state and a list of stacks to take args from. If there are enough args
  on each of the desired stacks, returns a map of the form {:state :args}, where
  :state is the new state and :args is a list of args from the stacks. If there
  aren't enough args on the stacks, returns :not-enough-args."
  [state stacks]
  (loop [state state
         stacks (reverse stacks)
         args '()]
    (if (empty? stacks)
      {:state state :args args}
      (let [stack (first stacks)]
        (if (empty-stack? state stack)
          :not-enough-args
          (recur (pop-stack state stack)
                 (rest stacks)
                 (conj args (peek-stack state stack))))))))

(defn make-push-instruction
  "A utility function for making Push instructions. Takes a state, the function
  to apply to the args, the stacks to take the args from, and the stack to return
  the result to. Applies the function to the args (taken from the stacks) and pushes
  the return value onto return-stack."
  [state function arg-stacks return-stack]
  (let [args-pop-result (get-args-from-stacks state arg-stacks)]
    (if (= args-pop-result :not-enough-args)
      state
      (let [result (apply function (:args args-pop-result))
            new-state (:state args-pop-result)]
        (push-to-stack new-state return-stack result)))))

;;;;;;;;;
;; Instructions

; (defn in1
;   "Pushes the input labeled :in1 on the inputs map onto the :exec stack."
;   [state]
;   (push-to-stack state :exec (:in1 (:input state))))

(defn integer_+
  [state]
  (make-push-instruction state +' [:integer :integer] :integer))


(defn integer_-
  [state]
  (make-push-instruction state -' [:integer :integer] :integer))

(defn integer_*
  [state]
  (make-push-instruction state *' [:integer :integer] :integer))

(defn integer_%
  [state]
  (make-push-instruction state
                         (fn [int1 int2]
                           (if (zero? int2)
                             int1
                             (quot int1 int2)))
                         [:integer :integer]
                         :integer))

(defn integer_=
  [state]
  (make-push-instruction state = [:integer :integer] :boolean))

(defn integer_<
  [state]
  (make-push-instruction state < [:integer :integer] :boolean))

(defn integer_>
  [state]
  (make-push-instruction state > [:integer :integer] :boolean))

(defn exec_dup
  [state]
  (if (empty-stack? state :exec)
    state
    (push-to-stack state :exec (first (:exec state)))))

(defn exec_if
  [state]
  (make-push-instruction state
                         #(if %1 %3 %2)
                         [:boolean :exec :exec]
                         :exec))

(defn boolean_and
  [state]
  (make-push-instruction state #(and %1 %2) [:boolean :boolean] :boolean))

(defn boolean_or
  [state]
  (make-push-instruction state #(or %1 %2) [:boolean :boolean] :boolean))

(defn boolean_not
  [state]
  (make-push-instruction state not [:boolean] :boolean))

(defn boolean_=
  [state]
  (make-push-instruction state = [:boolean :boolean] :boolean))

(defn element_at
  "Pushes the nth element in input list onto exec stack
   Doesn't modify input list"
  [state]
  (let [args-pop-result (get-args-from-stacks state [:integer])]
    (if (= args-pop-result :not-enough-args)
      state
      (let [nth-element (get (:input state) (first (:args args-pop-result)))]
        (if (= nth-element nil)
          state
          (push-to-stack (:state args-pop-result) :exec nth-element))))))

(defn element_swap
  "Swaps the two elements in input list
   If there is more than one element of the value in the list it picks the first one"
  [state]
  (let [args-pop-result (get-args-from-stacks state [:integer :integer])]
    (if (= args-pop-result :not-enough-args)
      state
      (let [i1 (.indexOf (:input state) (first (:args args-pop-result)))
            i2 (.indexOf (:input state) (second (:args args-pop-result)))]
        (if (and (>= i1 0)
                 (>= i2 0))
          (update
           (assoc state :input (swap (:input state) i1 i2))
           :swap-count
           inc)
          state)))))

(defn element_first
  "Pushes the first element of the input list onto exec stack"
  [state]
  (push-to-stack state :exec (first (:input state))))

(defn element_last
  "Pushes the last element of the input list onto exec stack"
  [state]
  (push-to-stack state :exec (last (:input state))))

(defn element_all
  "Pushes all the elements of the input list onto exec stack"
  [state]
  (last (not-lazy (map #(push-to-stack state :exec %) (:input state)))))


; (defn string_=
;   [state]
;   (make-push-instruction state = [:string :string] :boolean))

; (defn string_take
;   [state]
;   (make-push-instruction state
;                          #(apply str (take %1 %2))
;                          [:integer :string]
;                          :string))

; (defn string_drop
;   [state]
;   (make-push-instruction state
;                          #(apply str (drop %1 %2))
;                          [:integer :string]
;                          :string))

; (defn string_reverse
;   [state]
;   (make-push-instruction state
;                          #(apply str (reverse %))
;                          [:string]
;                          :string))

; (defn string_concat
;   [state]
;   (make-push-instruction state
;                          #(apply str (concat %1 %2))
;                          [:string :string]
;                          :string))

; (defn string_length
;   [state]
;   (make-push-instruction state count [:string] :integer))

; (defn string_includes?
  ; [state]
  ; (make-push-instruction state clojure.string/includes? [:string :string] :boolean))

;;;;;;;;;
;; Interpreter

(defn interpret-one-step
  "Takes a Push state and executes the next instruction on the exec stack."
  [state]
  (let [popped-state (pop-stack state :exec)
        first-raw (first (:exec state))
        first-instruction (if (symbol? first-raw)
                            (eval first-raw)
                            first-raw)]
    (cond
      (fn? first-instruction)
      (first-instruction popped-state)
      ;
      (integer? first-instruction)
      (push-to-stack popped-state :integer first-instruction)
      ;
      (string? first-instruction)
      (push-to-stack popped-state :string first-instruction)
      ;
      (seq? first-instruction)
      (update popped-state :exec #(concat %2 %1) first-instruction)
      ;
      (or (= first-instruction true) (= first-instruction false))
      (push-to-stack popped-state :boolean first-instruction)
      ;
      :else
      (throw (Exception. (str "Unrecognized Push instruction in program: "
                              first-instruction))))))

(defn interpret-program
  "Runs the given problem starting with the stacks in start-state."
  [program start-state step-limit]
  (loop [state (assoc start-state :exec program :step 1)]
    (if (or (empty? (:exec state))
            (> (:step state) step-limit))
      state
      (recur (assoc (interpret-one-step state) :step (+ (:step state) 1))))))

(defn push-from-plushy
  "Returns the Push program expressed by the given plushy representation."
  [plushy]
  (let [opener? #(and (vector? %) (= (first %) 'open))] ;; [open <n>] marks opens
    (loop [push () ;; iteratively build the Push program from the plushy
           plushy (mapcat #(if-let [n (get opens %)] [% ['open n]] [%]) plushy)]
      (if (empty? plushy)       ;; maybe we're done?
        (if (some opener? push) ;; done with plushy, but unclosed open
          (recur push '(close)) ;; recur with one more close
          push)                 ;; otherwise, really done, return push
        (let [i (first plushy)]
          (if (= i 'close)
            (if (some opener? push) ;; process a close when there's an open
              (recur (let [post-open (reverse (take-while (comp not opener?)
                                                          (reverse push)))
                           open-index (- (count push) (count post-open) 1)
                           num-open (second (nth push open-index))
                           pre-open (take open-index push)]
                       (if (= 1 num-open)
                         (concat pre-open [post-open])
                         (concat pre-open [post-open ['open (dec num-open)]])))
                     (rest plushy))
              (recur push (rest plushy))) ;; unmatched close, ignore
            (recur (concat push [i]) (rest plushy)))))))) ;; anything else

;;;;;;;;;
;; GP

(defn make-random-plushy
  "Creates and returns a new plushy."
  [instructions max-initial-plushy-size]
  (repeatedly (rand-int max-initial-plushy-size)
              #(rand-nth instructions)))

(defn tournament-selection
  "Selects an individual from the population using a tournament."
  [pop argmap]
  (let [tournament-size (:tournament-size argmap)
        tournament-set (take tournament-size (shuffle pop))]
    (apply min-key :total-error tournament-set)))

(defn lexicase-selection
  "Selects an individual from the population using lexicase selection."
  [pop argmap]
  (loop [survivors pop
         cases (shuffle (range (count (:errors (first pop)))))]
    (if (or (empty? cases)
            (empty? (rest survivors)))
      (rand-nth survivors)
      (let [min-err-for-case (apply min (map #(nth % (first cases))
                                             (map :errors survivors)))]
        (recur (filter #(= (nth (:errors %) (first cases)) min-err-for-case)
                       survivors)
               (rest cases))))))

(defn pareto-dominance-selection
  "Selects a random individiual from the pareto-dominance-front"
  [pop]
  (let [pareto-dominant (filter #(on-pareto-front? %1 pop) pop)]
    (rand-nth pareto-dominant))
  )

(defn select-parent 
  "Selects a parent from the population using the specified method."
  [pop argmap]
  (case (:parent-selection argmap)
    :tournament (tournament-selection pop argmap)
    :lexicase (lexicase-selection pop argmap)
    :paret-dominance (pareto-dominance-selection pop)))

(defn crossover
  "Crosses over two individuals using uniform crossover. Pads shorter one."
  [plushy-a plushy-b]
  (let [shorter (min-key count plushy-a plushy-b)
        longer (if (= shorter plushy-a)
                 plushy-b
                 plushy-a)
        length-diff (- (count longer) (count shorter))
        shorter-padded (concat shorter (repeat length-diff :crossover-padding))]
    (remove #(= % :crossover-padding)
            (map #(if (< (rand) 0.5) %1 %2)
                 shorter-padded
                 longer))))

(defn uniform-addition
  "Randomly adds new instructions before every instruction (and at the end of
  the plushy) with some probability."
  [plushy instructions]
  (let [rand-code (repeatedly (inc (count plushy))
                              (fn []
                                (if (< (rand) 0.05)
                                  (rand-nth instructions)
                                  :mutation-padding)))]
    (remove #(= % :mutation-padding)
            (interleave (conj plushy :mutation-padding)
                        rand-code))))

(defn uniform-deletion
  "Randomly deletes instructions from plushy at some rate."
  [plushy]
  (remove (fn [x] (< (rand) 0.05))
          plushy))

(defn new-individual
  "Returns a new individual produced by selection and variation of
  individuals in the population."
  [pop argmap]
  {:plushy
   (let [prob (rand)]
     (cond
       (< prob 0.5) (crossover (:plushy (select-parent pop argmap))
                               (:plushy (select-parent pop argmap)))
       (< prob 0.75) (uniform-addition (:plushy (select-parent pop argmap))
                                       (:instructions argmap))
       :else (uniform-deletion (:plushy (select-parent pop argmap)))))})

(defn report
  "Reports information each generation."
  [pop generation]
  (let [lowest-error (first pop)
        lowest-swap (first (sort-by :swaps pop))
        pareto-dominant (filter #(on-pareto-front? %1 pop) pop)]
    (println "-------------------------------------------------------")
    (println "               Report for Generation" generation)
    (println "-------------------------------------------------------")
    (print "Best program: ") (prn (push-from-plushy (:plushy lowest-error)))
    (println "Best total error(swaps, error):" (:swaps lowest-error) (:total-error lowest-error))
    (println "Best errors:" (:errors lowest-error))
    (println "Lowest swaps(swap, error):" (:swaps lowest-swap)  (:total-error lowest-swap))
    (print "Pareto-frontier(swap, error):")
    (println (map #(list (:swaps %1) (:total-error %1)) pareto-dominant))
    (println "")

    (println)))

(defn propel-gp
  "Main GP loop."
  [{:keys [population-size max-generations error-function instructions
           max-initial-plushy-size]
    :as argmap}]
  (println "Starting GP with args:" argmap)
  (loop [generation 0
         population (repeatedly
                     population-size
                     #(hash-map :plushy
                                (make-random-plushy instructions
                                                    max-initial-plushy-size)))]
    (let [input-vector (not-lazy-vector (repeatedly (:input-list-size argmap) #(rand-int 100)))
          evaluated-pop (sort-by :total-error
                                 (map #(error-function (:step-limit argmap) input-vector %)
                                      population))]
      (report evaluated-pop generation)
      (cond
        (zero? (:total-error (first evaluated-pop))) (println "SUCCESS")
        (>= generation max-generations) nil
        :else (recur (inc generation)
                     (repeatedly population-size
                                 #(new-individual evaluated-pop argmap)))))))

;;;;;;;;;
;; Problem: f(x) = 7x^2 - 20x + 13

(defn target-function-hard
  "Target function: f(x) = 7x^2 - 20x + 13"
  [x]
  (+ (* 7 x x)
     (* -20 x)
     13))

(defn target-function
  "Target function: f(x) = x^3 + x + 3"
  [x]
  (+ (* x x x)
     x
     3))

(defn regression-error-function
  "Finds the behaviors and errors of an individual: Error is the absolute deviation between the target output value and the program's selected behavior, or 1000000 if no behavior is produced. The behavior is here defined as the final top item on the :integer stack."
  [argmap individual]
  (let [program (push-from-plushy (:plushy individual))
        inputs (range -10 11)
        correct-outputs (map target-function inputs)
        outputs (map (fn [input]
                       (peek-stack
                        (interpret-program
                         program
                         (assoc empty-push-state :input {:in1 input})
                         (:step-limit argmap))
                        :integer))
                     inputs)
        errors (map (fn [correct-output output]
                      (if (= output :no-stack-item)
                        1000000
                        (abs (- correct-output output))))
                    correct-outputs
                    outputs)]
    (assoc individual
           :behaviors outputs
           :errors errors
           :total-error (apply +' errors))))

;;;;;;;;;
;; String classification

(defn string-classification-error-function
  "Finds the behaviors and errors of an individual: Error is 0 if the value and the program's selected behavior match, or 1 if they differ, or 1000000 if no behavior is produced. The behavior is here defined as the final top item on the :boolean stack."
  [argmap individual]
  (let [program (push-from-plushy (:plushy individual))
        inputs ["GCG" "GACAG" "AGAAG" "CCCA" "GATTACA" "TAGG" "GACT"]
        correct-outputs [false false false false true true true]
        outputs (map (fn [input]
                       (peek-stack
                        (interpret-program
                         program
                         (assoc empty-push-state :input {:in1 input})
                         (:step-limit argmap))
                        :boolean))
                     inputs)
        errors (map (fn [correct-output output]
                      (if (= output :no-stack-item)
                        1000000
                        (if (= correct-output output)
                          0
                          1)))
                    correct-outputs
                    outputs)]
    (assoc individual
           :behaviors outputs
           :errors errors
           :total-error (apply +' errors))))

;;;;;;;;;;;;
;; Sort error

(defn sort-error-function
  "Returns the error function"
  [step-limit input-vector individual]
  (let [program (push-from-plushy (:plushy individual))
        correct-output (sort input-vector)
        new-state (interpret-program
                   program
                   (assoc empty-push-state :input input-vector)
                   step-limit)
        output (:input new-state)
        error (map #(abs (- %1 %2)) correct-output output)]
    (assoc individual
           :swaps (:swap-count new-state)
           :errors error
           :total-error (/ (apply +' error) (apply +' input-vector)))))

(defn -main
  "Runs propel-gp, giving it a map of arguments."
  [& args]
  (binding [*ns* (the-ns 'propel.core)]
    (propel-gp (update-in (merge {:instructions sort-instructions
                                  :error-function sort-error-function
                                  :max-generations 120000
                                  :population-size 300
                                  :max-initial-plushy-size 150
                                  :step-limit 500
                                  :input-list-size 20
                                  :parent-selection :tournament
                                  :tournament-size 5}
                                 (apply hash-map
                                        (map read-string args)))
                          [:error-function]
                          #(if (fn? %) % (eval %))))))
