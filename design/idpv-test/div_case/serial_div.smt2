; SMT-LIBv2 description generated by Yosys 0.40+4 (git sha1 47bdb3e32, clang++ 14.0.0-1ubuntu1.1 -fPIC -Os)
; yosys-smt2-module serial_divide_uu
(declare-sort |serial_divide_uu_s| 0)
(declare-fun |serial_divide_uu_is| (|serial_divide_uu_s|) Bool)
; yosys-smt2-witness {"offset": 0, "path": ["\\divide_count"], "smtname": 0, "smtoffset": 0, "type": "reg", "width": 5}
(declare-fun |serial_divide_uu#0| (|serial_divide_uu_s|) (_ BitVec 5)) ; \divide_count
; yosys-smt2-register divide_count 5
(define-fun |serial_divide_uu_n divide_count| ((state |serial_divide_uu_s|)) (_ BitVec 5) (|serial_divide_uu#0| state))
; yosys-smt2-witness {"offset": 0, "path": ["\\quotient_reg"], "smtname": 1, "smtoffset": 0, "type": "reg", "width": 16}
(declare-fun |serial_divide_uu#1| (|serial_divide_uu_s|) (_ BitVec 16)) ; \quotient_reg
; yosys-smt2-register quotient_reg 16
(define-fun |serial_divide_uu_n quotient_reg| ((state |serial_divide_uu_s|)) (_ BitVec 16) (|serial_divide_uu#1| state))
; yosys-smt2-witness {"offset": 0, "path": ["\\quotient"], "smtname": 2, "smtoffset": 0, "type": "reg", "width": 16}
(declare-fun |serial_divide_uu#2| (|serial_divide_uu_s|) (_ BitVec 16)) ; \quotient
; yosys-smt2-register quotient 16
(define-fun |serial_divide_uu_n quotient| ((state |serial_divide_uu_s|)) (_ BitVec 16) (|serial_divide_uu#2| state))
; yosys-smt2-witness {"offset": 0, "path": ["\\grand_divisor"], "smtname": 3, "smtoffset": 0, "type": "reg", "width": 23}
(declare-fun |serial_divide_uu#3| (|serial_divide_uu_s|) (_ BitVec 23)) ; \grand_divisor
; yosys-smt2-register grand_divisor 23
(define-fun |serial_divide_uu_n grand_divisor| ((state |serial_divide_uu_s|)) (_ BitVec 23) (|serial_divide_uu#3| state))
; yosys-smt2-witness {"offset": 0, "path": ["\\grand_dividend"], "smtname": 4, "smtoffset": 0, "type": "reg", "width": 16}
(declare-fun |serial_divide_uu#4| (|serial_divide_uu_s|) (_ BitVec 16)) ; \grand_dividend
; yosys-smt2-register grand_dividend 16
(define-fun |serial_divide_uu_n grand_dividend| ((state |serial_divide_uu_s|)) (_ BitVec 16) (|serial_divide_uu#4| state))
; yosys-smt2-witness {"offset": 0, "path": ["\\done_o"], "smtname": 5, "smtoffset": 0, "type": "reg", "width": 1}
(declare-fun |serial_divide_uu#5| (|serial_divide_uu_s|) (_ BitVec 1)) ; \done_o
; yosys-smt2-output done_o 1
; yosys-smt2-register done_o 1
(define-fun |serial_divide_uu_n done_o| ((state |serial_divide_uu_s|)) Bool (= ((_ extract 0 0) (|serial_divide_uu#5| state)) #b1))
; yosys-smt2-output quotient_o 16
(define-fun |serial_divide_uu_n quotient_o| ((state |serial_divide_uu_s|)) (_ BitVec 16) (|serial_divide_uu#2| state))
(declare-fun |serial_divide_uu#6| (|serial_divide_uu_s|) (_ BitVec 8)) ; \divisor_i
; yosys-smt2-input divisor_i 8
; yosys-smt2-witness {"offset": 0, "path": ["\\divisor_i"], "smtname": "divisor_i", "smtoffset": 0, "type": "input", "width": 8}
(define-fun |serial_divide_uu_n divisor_i| ((state |serial_divide_uu_s|)) (_ BitVec 8) (|serial_divide_uu#6| state))
(declare-fun |serial_divide_uu#7| (|serial_divide_uu_s|) (_ BitVec 16)) ; \dividend_i
; yosys-smt2-input dividend_i 16
; yosys-smt2-witness {"offset": 0, "path": ["\\dividend_i"], "smtname": "dividend_i", "smtoffset": 0, "type": "input", "width": 16}
(define-fun |serial_divide_uu_n dividend_i| ((state |serial_divide_uu_s|)) (_ BitVec 16) (|serial_divide_uu#7| state))
(declare-fun |serial_divide_uu#8| (|serial_divide_uu_s|) Bool) ; \divide_i
; yosys-smt2-input divide_i 1
; yosys-smt2-witness {"offset": 0, "path": ["\\divide_i"], "smtname": "divide_i", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |serial_divide_uu_n divide_i| ((state |serial_divide_uu_s|)) Bool (|serial_divide_uu#8| state))
(declare-fun |serial_divide_uu#9| (|serial_divide_uu_s|) Bool) ; \rst_i
; yosys-smt2-input rst_i 1
; yosys-smt2-witness {"offset": 0, "path": ["\\rst_i"], "smtname": "rst_i", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |serial_divide_uu_n rst_i| ((state |serial_divide_uu_s|)) Bool (|serial_divide_uu#9| state))
(declare-fun |serial_divide_uu#10| (|serial_divide_uu_s|) Bool) ; \clk_en_i
; yosys-smt2-input clk_en_i 1
; yosys-smt2-witness {"offset": 0, "path": ["\\clk_en_i"], "smtname": "clk_en_i", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |serial_divide_uu_n clk_en_i| ((state |serial_divide_uu_s|)) Bool (|serial_divide_uu#10| state))
(declare-fun |serial_divide_uu#11| (|serial_divide_uu_s|) Bool) ; \clk_i
; yosys-smt2-input clk_i 1
; yosys-smt2-clock clk_i posedge
; yosys-smt2-witness {"offset": 0, "path": ["\\clk_i"], "smtname": "clk_i", "smtoffset": 0, "type": "posedge", "width": 1}
; yosys-smt2-witness {"offset": 0, "path": ["\\clk_i"], "smtname": "clk_i", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |serial_divide_uu_n clk_i| ((state |serial_divide_uu_s|)) Bool (|serial_divide_uu#11| state))
(define-fun |serial_divide_uu#12| ((state |serial_divide_uu_s|)) Bool (= (|serial_divide_uu#0| state) #b01111)) ; $eq$serial_divide_uu.v:185$5_Y
(define-fun |serial_divide_uu#13| ((state |serial_divide_uu_s|)) (_ BitVec 1) (ite (|serial_divide_uu#12| state) #b1 (|serial_divide_uu#5| state))) ; $procmux$85_Y
(define-fun |serial_divide_uu#14| ((state |serial_divide_uu_s|)) Bool (not (or  (= ((_ extract 0 0) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 1 1) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 2 2) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 3 3) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 4 4) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 5 5) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 6 6) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 7 7) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 8 8) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 9 9) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 10 10) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 11 11) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 12 12) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 13 13) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 14 14) (|serial_divide_uu#7| state)) #b1) (= ((_ extract 15 15) (|serial_divide_uu#7| state)) #b1)))) ; $eq$serial_divide_uu.v:169$2_Y
(define-fun |serial_divide_uu#15| ((state |serial_divide_uu_s|)) (_ BitVec 1) (ite (|serial_divide_uu#14| state) #b1 (|serial_divide_uu#5| state))) ; $procmux$89_Y
(define-fun |serial_divide_uu#16| ((state |serial_divide_uu_s|)) (_ BitVec 1) (ite (|serial_divide_uu#8| state) (|serial_divide_uu#15| state) (|serial_divide_uu#13| state))) ; $procmux$91_Y
(define-fun |serial_divide_uu#17| ((state |serial_divide_uu_s|)) (_ BitVec 1) (ite (|serial_divide_uu#10| state) (|serial_divide_uu#16| state) (|serial_divide_uu#5| state))) ; $procmux$93_Y
(define-fun |serial_divide_uu#18| ((state |serial_divide_uu_s|)) (_ BitVec 1) (ite (|serial_divide_uu#9| state) #b0 (|serial_divide_uu#17| state))) ; $procmux$96_Y
(define-fun |serial_divide_uu#19| ((state |serial_divide_uu_s|)) (_ BitVec 24) (bvsub (concat #b00000000 (|serial_divide_uu#4| state)) (concat #b0 (|serial_divide_uu#3| state)))) ; $sub$serial_divide_uu.v:206$10_Y
(define-fun |serial_divide_uu#20| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (= ((_ extract 23 23) (|serial_divide_uu#19| state)) #b1) (|serial_divide_uu#4| state) ((_ extract 15 0) (|serial_divide_uu#19| state)))) ; $procmux$68_Y
(define-fun |serial_divide_uu#21| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#12| state) (|serial_divide_uu#4| state) (|serial_divide_uu#20| state))) ; $procmux$71_Y
(define-fun |serial_divide_uu#22| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#14| state) (|serial_divide_uu#4| state) (|serial_divide_uu#7| state))) ; $procmux$75_Y
(define-fun |serial_divide_uu#23| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#8| state) (|serial_divide_uu#22| state) (|serial_divide_uu#21| state))) ; $procmux$77_Y
(define-fun |serial_divide_uu#24| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#10| state) (|serial_divide_uu#23| state) (|serial_divide_uu#4| state))) ; $procmux$79_Y
(define-fun |serial_divide_uu#25| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#9| state) #b0000000000000000 (|serial_divide_uu#24| state))) ; $procmux$82_Y
(define-fun |serial_divide_uu#26| ((state |serial_divide_uu_s|)) (_ BitVec 23) (ite (|serial_divide_uu#12| state) (|serial_divide_uu#3| state) (concat #b0 ((_ extract 22 1) (|serial_divide_uu#3| state))))) ; $procmux$55_Y
(define-fun |serial_divide_uu#27| ((state |serial_divide_uu_s|)) (_ BitVec 23) (ite (|serial_divide_uu#14| state) (|serial_divide_uu#3| state) (concat #b00000000 (concat (|serial_divide_uu#6| state) #b0000000)))) ; $procmux$59_Y
(define-fun |serial_divide_uu#28| ((state |serial_divide_uu_s|)) (_ BitVec 23) (ite (|serial_divide_uu#8| state) (|serial_divide_uu#27| state) (|serial_divide_uu#26| state))) ; $procmux$61_Y
(define-fun |serial_divide_uu#29| ((state |serial_divide_uu_s|)) (_ BitVec 23) (ite (|serial_divide_uu#10| state) (|serial_divide_uu#28| state) (|serial_divide_uu#3| state))) ; $procmux$63_Y
(define-fun |serial_divide_uu#30| ((state |serial_divide_uu_s|)) (_ BitVec 23) (ite (|serial_divide_uu#9| state) #b00000000000000000000000 (|serial_divide_uu#29| state))) ; $procmux$66_Y
(define-fun |serial_divide_uu#31| ((state |serial_divide_uu_s|)) (_ BitVec 1) (bvnot ((_ extract 23 23) (|serial_divide_uu#19| state)))) ; $not$serial_divide_uu.v:208$11_Y
(define-fun |serial_divide_uu#32| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (= ((_ extract 0 0) (|serial_divide_uu#5| state)) #b1) (|serial_divide_uu#2| state) (concat ((_ extract 14 0) (|serial_divide_uu#2| state)) (|serial_divide_uu#31| state)))) ; $procmux$40_Y
(define-fun |serial_divide_uu#33| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#12| state) (|serial_divide_uu#32| state) (concat ((_ extract 14 0) (|serial_divide_uu#2| state)) (|serial_divide_uu#31| state)))) ; $procmux$42_Y
(define-fun |serial_divide_uu#34| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#8| state) #b0000000000000000 (|serial_divide_uu#33| state))) ; $procmux$47_Y
(define-fun |serial_divide_uu#35| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#10| state) (|serial_divide_uu#34| state) (|serial_divide_uu#2| state))) ; $procmux$49_Y
(define-fun |serial_divide_uu#36| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#9| state) #b0000000000000000 (|serial_divide_uu#35| state))) ; $procmux$52_Y
(define-fun |serial_divide_uu#37| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (= ((_ extract 0 0) (|serial_divide_uu#5| state)) #b1) (|serial_divide_uu#1| state) (concat ((_ extract 14 0) (|serial_divide_uu#2| state)) (|serial_divide_uu#31| state)))) ; $procmux$27_Y
(define-fun |serial_divide_uu#38| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#12| state) (|serial_divide_uu#37| state) (|serial_divide_uu#1| state))) ; $procmux$29_Y
(define-fun |serial_divide_uu#39| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#8| state) (|serial_divide_uu#1| state) (|serial_divide_uu#38| state))) ; $procmux$32_Y
(define-fun |serial_divide_uu#40| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#10| state) (|serial_divide_uu#39| state) (|serial_divide_uu#1| state))) ; $procmux$34_Y
(define-fun |serial_divide_uu#41| ((state |serial_divide_uu_s|)) (_ BitVec 16) (ite (|serial_divide_uu#9| state) (|serial_divide_uu#1| state) (|serial_divide_uu#40| state))) ; $procmux$37_Y
(define-fun |serial_divide_uu#42| ((state |serial_divide_uu_s|)) (_ BitVec 32) (bvadd (concat #b000000000000000000000000000 (|serial_divide_uu#0| state)) #b00000000000000000000000000000001)) ; $add$serial_divide_uu.v:201$9_Y
(define-fun |serial_divide_uu#43| ((state |serial_divide_uu_s|)) (_ BitVec 5) (ite (|serial_divide_uu#12| state) (|serial_divide_uu#0| state) ((_ extract 4 0) (|serial_divide_uu#42| state)))) ; $procmux$13_Y
(define-fun |serial_divide_uu#44| ((state |serial_divide_uu_s|)) (_ BitVec 5) (ite (|serial_divide_uu#14| state) (|serial_divide_uu#0| state) #b00000)) ; $procmux$17_Y
(define-fun |serial_divide_uu#45| ((state |serial_divide_uu_s|)) (_ BitVec 5) (ite (|serial_divide_uu#8| state) (|serial_divide_uu#44| state) (|serial_divide_uu#43| state))) ; $procmux$19_Y
(define-fun |serial_divide_uu#46| ((state |serial_divide_uu_s|)) (_ BitVec 5) (ite (|serial_divide_uu#10| state) (|serial_divide_uu#45| state) (|serial_divide_uu#0| state))) ; $procmux$21_Y
(define-fun |serial_divide_uu#47| ((state |serial_divide_uu_s|)) (_ BitVec 5) (ite (|serial_divide_uu#9| state) #b00000 (|serial_divide_uu#46| state))) ; $procmux$24_Y
(define-fun |serial_divide_uu_a| ((state |serial_divide_uu_s|)) Bool true)
(define-fun |serial_divide_uu_u| ((state |serial_divide_uu_s|)) Bool true)
(define-fun |serial_divide_uu_i| ((state |serial_divide_uu_s|)) Bool true)
(define-fun |serial_divide_uu_h| ((state |serial_divide_uu_s|)) Bool true)
(define-fun |serial_divide_uu_t| ((state |serial_divide_uu_s|) (next_state |serial_divide_uu_s|)) Bool (and
  (= (|serial_divide_uu#18| state) (|serial_divide_uu#5| next_state)) ; $procdff$98 \done_o
  (= (|serial_divide_uu#25| state) (|serial_divide_uu#4| next_state)) ; $procdff$99 \grand_dividend
  (= (|serial_divide_uu#30| state) (|serial_divide_uu#3| next_state)) ; $procdff$100 \grand_divisor
  (= (|serial_divide_uu#36| state) (|serial_divide_uu#2| next_state)) ; $procdff$101 \quotient
  (= (|serial_divide_uu#41| state) (|serial_divide_uu#1| next_state)) ; $procdff$102 \quotient_reg
  (= (|serial_divide_uu#47| state) (|serial_divide_uu#0| next_state)) ; $procdff$103 \divide_count
)) ; end of module serial_divide_uu
; yosys-smt2-topmod serial_divide_uu
; end of yosys output
