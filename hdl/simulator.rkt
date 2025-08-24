#lang racket

; simulator/runtime/backend for the HDL
; Simulates a logic circuit.

(module+ test (require rackunit))
(provide
 circuit
 circuit?
 (struct-out gate)
 port?
 (struct-out input-port)
 (struct-out output-port)
 (struct-out wire)
 circuit-debug
 (contract-out
  [circuit-run! (-> circuit? void?)]
  [circuit-step! (-> circuit? void?)]
  [circuit-reset! (-> circuit? void?)]
  [circuit-port-powered? (-> circuit? port? boolean?)]
  [set-circuit-port-powered?! (-> circuit? port? boolean? void?)]
  [circuit-union (->* () #:rest (listof circuit?) circuit?)]
  [circuit->datum (-> circuit? any)]))
(require racket/match)

; A circuit is a network of logic gates connected by wires as well as some state
; describing which parts have power flowing.
; See circuit-step! for semantics.

; a Circuit is a
(struct circuit [gates wires [powered-ports #:mutable]])
; where
; gates is a list of gates in the circuit
; wires is a list of wires inside the circuit
; powered-ports is a seteq of ports that are receiving or sending power. This is the state.
; Represents a running logic circuit.

; a Gate is a
(struct gate [name inputs output proc] #:property prop:object-name 0)
; where
; inputs is a list of input ports
; output is an output port
; proc is a (boolean ... -> boolean)
; where the input arity is the same as the number of input ports
; Represents a logic gate

; A Port is one of
(struct port [name] #:property prop:object-name 0)

(struct input-port port [])
(struct output-port port [])
; Represents the interfaces of a logic gate

; A Wire is a
(struct wire [output input]
  #:transparent
  #:guard (lambda (output input name)
            (unless (input-port? input)
              (error "wire input must be an input port"))
            (unless (output-port? output)
              (error "wire output must be an output port"))
            (values output input)))
; where
; input is an input port
; output is an output port
; Represents a connection between two logic gates.
; Power flows from output to input.

; example:
; a-->|\
;     | |-->out
; b-->|/
(define and-a (input-port 'a))
(define and-b (input-port 'b))
(define and-out (output-port 'out))
(define and-circuit
  (let ([and-gate (gate 'and (list and-a and-b) and-out (lambda (a b) (and a b)))])
    (circuit (list and-gate) (list) (seteq))))

(module+ test
  (test-case "and-gate full use"
    (circuit-reset! and-circuit)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #f)

    (circuit-reset! and-circuit)
    (set-circuit-port-powered?! and-circuit and-a #t)
    (set-circuit-port-powered?! and-circuit and-b #f)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #f)

    (circuit-reset! and-circuit)
    (set-circuit-port-powered?! and-circuit and-a #t)
    (set-circuit-port-powered?! and-circuit and-b #t)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #t)

    (circuit-reset! and-circuit)
    (set-circuit-port-powered?! and-circuit and-a #f)
    (set-circuit-port-powered?! and-circuit and-b #t)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #f)))

; Circuit -> Void
; Run the circuit until it stabilizes (everything stops changing).
; Not all circuits will stabilize. In this case, this procedure will not terminate.
(define (circuit-run! circ)
  (let loop ([old-powereds (circuit-powered-ports circ)])
    (circuit-step! circ)
    (define new-powereds (circuit-powered-ports circ))
    (unless (equal? old-powereds new-powereds)
        (loop new-powereds))))

; Circuit -> Void
; Step the circuit.
; Update each output according to its current inputs and logic gate procedure.
; Update each input according to the output(s) connected to it and their NEW values.
; O(gates * wires) time. hashes might get you down to O(gates + wires), which is effectively O(wires) since gates ~~ k*wires.
(define (circuit-step! circ)
  (define powered-outputs
    ; O(gates) time
    (for/seteq ([gat (circuit-gates circ)]
                #:when (circuit-gate-run circ gat))
      (gate-output gat)))
  (define powered-inputs
    ; O(wires * powered-outputs) time
    (for/fold ([powered-inputs (seteq)])
              ([out powered-outputs])
      ; O(wires) time (can be improved to O(output-children) with hashes)
      (define ins (for/seteq ([in (circuit-output-children circ out)]) in))
      (set-union powered-inputs ins)))
  (define new-powereds (set-union powered-outputs powered-inputs))
  (set-circuit-powered-ports! circ new-powereds))

; Power off all ports in the circuit
(define (circuit-reset! circ)
  (set-circuit-powered-ports! circ (seteq)))

; Circuit Gate -> Boolean
; Should the gate's output be powered based on its inputs?
; Runs the gate's procedure with the current values of its input ports.
; time complexity is O(inputs)
(define (circuit-gate-run circ gat)
  (match-define (gate _ inputs _ proc) gat)
  (apply proc (for/list ([in inputs]) (circuit-port-powered? circ in))))

; Circuit OutputPort -> (Listof InputPort)
; Finds the inputs that the given output is directly connected to through wires
; O(wires) time
(define (circuit-output-children circ out)
  (for/list ([wir (circuit-wires circ)]
             #:when (eq? out (wire-output wir)))
    (wire-input wir)))

; Circuit Gate -> Boolean
; Is the gate's output powered?
(define (circuit-gate-powered? circ gat)
  (circuit-port-powered? circ (gate-output gat)))

; Circuit Port -> Boolean
; Is the port powered?
(define (circuit-port-powered? circ prt)
  (set-member? (circuit-powered-ports circ) prt))

; Circuit Port Boolean -> Void
; Power the port on or off.
(define (set-circuit-port-powered?! circ prt powered?)
  (define powereds (circuit-powered-ports circ))
  (set-circuit-powered-ports! circ
                              (if powered?
                                  (set-add powereds prt)
                                  (set-remove powereds prt))))

(define-syntax-rule
  (circuit-debug circ prt ...)
  (begin
    (displayln (format "~a: ~a" 'prt (circuit-port-powered? circ prt)))
    ...))

(module+ test
  (test-case "clock stepping"
    ; clock that changes every other tick
    ; can make a 1-tick clock by hooking this up to an xor
    (define in (input-port 'in))
    (define out (output-port 'out))
    (define not-gate (gate 'not (list in) out not))
    (define clock (circuit (list not-gate) (list (wire out in)) (seteq)))
    (check-equal? (circuit-port-powered? clock out) #f)
    (check-equal? (circuit-port-powered? clock in) #f)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #t)
    (check-equal? (circuit-port-powered? clock in) #t)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #f)
    (check-equal? (circuit-port-powered? clock in) #f)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #t)
    (check-equal? (circuit-port-powered? clock in) #t)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #f)
    (check-equal? (circuit-port-powered? clock in) #f))
  (test-case "nand"
    (define a (input-port 'a))
    (define b (input-port 'b))
    (define and-out (output-port 'and-out))
    (define not-in (input-port 'not-in))
    (define out (output-port 'out))
    (define and-gate (gate 'and (list a b) and-out (lambda (a b) (and a b))))
    (define not-gate (gate 'not (list not-in) out not))
    (define nand (circuit (list and-gate not-gate)
                          (list (wire and-out not-in))
                          (seteq)))

    (set-circuit-powered-ports! nand (seteq a b))
    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq and-out not-in out))
    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq))
    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq out))

    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq out))))

; Circuit ... -> Circuit
(define (circuit-union . circs)
  (for/fold ([u (circuit (list) (list) (seteq))])
            ([circ circs])
    (circuit-union/bin u circ)))

; Circuit Circuit -> Circuit
(define (circuit-union/bin u circ)
  (define powereds (mutable-seteq))
  (set-union! powereds (circuit-powered-ports u) (circuit-powered-ports circ))
  (circuit (append (circuit-gates u) (circuit-gates circ))
           (append (circuit-wires u) (circuit-wires circ))
           powereds))

; Circuit -> Datum
; for debugging
(define (circuit->datum circ)
  (list 'circuit
        (cons 'gates (for/list ([gat (circuit-gates circ)])
                       (gate->datum gat)))
        (cons 'powered-ports (for/list ([prt (circuit-powered-ports circ)])
                               (object-name prt)))
        (cons 'wires (for/list ([wir (circuit-wires circ)])
                       (wire->datum wir)))))

; Gate -> Datum
; for debugging
(define (gate->datum gat)
  (list (object-name gat) (append (for/list ([prt (gate-inputs gat)]) (object-name prt))
                                  '(->)
                                  (list (object-name (gate-output gat))))))

; Wire -> Datum
; for debugging
(define (wire->datum wir)
  (list (object-name (wire-output wir))
        '->
        (object-name (wire-input wir))))
