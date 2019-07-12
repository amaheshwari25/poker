/*
* Arya Maheshwari
* 5/13/19
* Simulates decision-making in the first round of a standard Texas hold'em poker game 
   with an expert system providing advice on what to do right after receiving the first two cards.
* This expert system's knowledge comes from interviews with Mr. Hurshman, who organizes a poker tournament every year
   and has extensive experience in Texas hold'em gameplay. The various thresholds and guidelines for rules are derived from his gameplay strategies.
*/

(clear)
(reset)

(batch utilities.clp) ; user input functions

; the two-part Card template is used to structure and group the information users input regarding their cards
(deftemplate Card (slot val) (slot suit))

/**
* Various pieces of information about the game elicited via backward chaining
**/

(do-backward-chaining stacksize)
(do-backward-chaining Card)
(do-backward-chaining position)
(do-backward-chaining numplayers)
(do-backward-chaining betpreflop)
(do-backward-chaining smallblind)
(do-backward-chaining bigblind)

(defglobal ?*SMALL_BLIND* = 1) ; the small blind position (a strong position to be in) is defined to be 1
(defglobal ?*BIG_BLIND* = 2)   ; the big blind position (a strong position to be in) is defined to be 2
(defglobal ?*GUN* = 3)         ; the person right after the big blind acts first, and so is "under the gun" in a weak position
(defglobal ?*AFTERGUN* = 4)    ; the person who acts after the gun but is not small or big blind (if there are > 3 players)

(defglobal ?*MIN_PLAYERS* = 3) ; this expert system assumes at least 3 players in a game

; numerical values that represent the Ace (A), King (K), Queen (Q), and Jack (J) cards
(defglobal ?*A* = 14)
(defglobal ?*K* = 13)
(defglobal ?*Q* = 12)
(defglobal ?*J* = 11)

; these constants represent scale values that can judge how much money you have compared to the preflop bet
(defglobal ?*HIGHMONEY* = 16) ; for instance, a very large stack size in a certain round is set at 16 times the preflop bet 
(defglobal ?*GOODMONEY* = 8)
(defglobal ?*LOWMONEY* = 4)
(defglobal ?*CRITICALMONEY* = 2)

; for cases of raising (explained later), these constants specify how many times the blinds you should raise
(defglobal ?*BIGBLIND_MEDRAISE* = 5)
(defglobal ?*BIGBLIND_LARGERAISE* = 10)

(defglobal ?*A2DIST* = 12) ; the numerical distance between the value for an Ace (14) and a 2 is 12, which needs to be checked for connecting cards

/**
* Backward-chaining rules for input on state of the game, to find the above backward-chained facts
**/

(defrule getStackSize "Ask about the player's stack size"
   (need-stacksize ?)
=>
   (bind ?ss (ask "Enter the size of your chip stack (total value of all chips): "))
   (while (not (and (integerp ?ss) (> ?ss 0)))
      (printout t "Invalid input. Please try again and enter a positive integer." crlf)
      (bind ?ss (ask "Enter the size of your chip stack: "))
   )

   (printout t crlf)

   (assert (stacksize ?ss))
) ; defrule getStackSize

(defrule getPocketCards "Ask about a player's pocket cards"
   (need-Card (val ?) (suit ?))
=>
   (bind ?card1 (askline "Enter your first card, formatted as indicated earlier (e.g. King of clubs = K C): "))
   (while (not (validCard ?card1))
      (printout t "Invalid input. Please try again and enter a valid card format." crlf)
      (bind ?card1 (askline "Enter your first card: "))
   )

   (bind ?card2 (askline "Enter your second card, formatted as indicated earlier: "))
   (bind ?carditems1 (explode$ (lowcase ?card1)))
   (bind ?carditems2 (explode$ (lowcase ?card2)))

   (while (or (eq ?carditems1 ?carditems2) (not (validCard ?card2)))
      (if (eq ?carditems1 ?carditems2) then (printout t "That seems like the same card. Please try again." crlf)
       else (printout t "Invalid input. Please try again and enter a valid card format." crlf)
      )
      (bind ?card2 (askline "Enter your second card: "))
      (bind ?carditems2 (explode$ (lowcase ?card2)))
   )

   (printout t crlf)
   
   (bind ?carditems1 (explode$ (lowcase ?card1)))
   (bind ?carditems2 (explode$ (lowcase ?card2)))

   (assert (Card (val (nth$ 1 ?carditems1)) (suit (nth$ 2 ?carditems1))))
   (assert (Card (val (nth$ 1 ?carditems2)) (suit (nth$ 2 ?carditems2))))

) ; defrule getPocketCards

(defrule getPlayerPos "Ask about a player's position"
   (need-position ?)
   (numplayers ?n)
=>
   (bind ?pos (ask "Enter your starting position (before the round began) in the round (small blind is 1, big blind is 2, and so forth): "))
   (while (not (and (integerp ?pos) (> ?pos 0) (<= ?pos ?n)))
      (printout t "Invalid input. Please try again and input a positive integer no bigger than the number of players." crlf)
      (bind ?pos (ask "Enter your position in the hand: "))
   )

   (printout t crlf)

   (assert (position ?pos))
) ; defrule getPlayerPos

(defrule getNumPlayers "Ask about the number of players in the round"
   (need-numplayers ?)
=>
   (bind ?nump (ask "Enter the number of players playing this round: "))
   (while (not (and (integerp ?nump) (>= ?nump ?*MIN_PLAYERS*)))
      (printout t "Invalid input. Please try again and input a positive integer greater than 2." crlf)
      (bind ?nump (ask "Enter the number of players playing this round: "))
   )
   (printout t crlf)

   (assert (numplayers ?nump))
) ; defrule getNumPlayers

(defrule getBetPreflop "Ask about the pre-flop bet to call"
   (need-betpreflop ?)
=>
   (bind ?bet (ask "What's the pre-flop bet to call (if you are big blind and no one has raised, then this is 0)? "))
   (while (not (and (integerp ?bet) (>= ?bet 0) ))
      (printout t "Invalid input. Please try again and input a non-negative integer." crlf)
      (bind ?bet (ask "What's the pre-flop bet to call? "))
   )
   (printout t crlf)

   (assert (betpreflop ?bet))
) ; defrule getBetPreflop

(defrule getBlinds "Ask about the size of the small and big blinds"
   (or (need-smallblind ?)(need-bigblind ?))
=> 
   (bind ?smallblind (ask "Enter the small blind amount (big blind is assumed to be double): "))
   (while (not (and (integerp ?smallblind) (> ?smallblind 0)))
      (printout t "Invalid input. Please try again and enter a positive integer." crlf)
      (bind ?smallblind (ask "Enter the small blind amount: "))
   )

   (printout t crlf)

   (assert (smallblind ?smallblind))
   (assert (bigblind (integer (* 2 ?smallblind)))) ; the big blind value is double the small blind value
) ; defrule getBlinds

/**
* Rules for pre-flop (3 cards) play
* All of the details of these rules are derived from the guidelines followed by the expert, Mr. Hurshman, when he plays Texas Hold'em.
* Tier 1 is the set of the very best hands, and tier 5 is the set of the worst hands ("trash" hands)
**/


(defrule preflop-tier1 "Determine whether this pocket hand is a tier 1 hand"
   ?eval <- (preflopeval FALSE)

   (or (pocketpair ?v1&?*A*)                                           ; pair of aces
       (pocketpair ?v1&?*K*)                                           ; pair of kings 

       (and (suitedconn ?v1 ?v2) (test (= (+ ?v1 ?v2) (+ ?*A* ?*K*)))) ; checks for a-k suited by checking sum, which cannot be reached in another way
   )
=>
   (assert (tier 1))
   (assert (preflopeval TRUE))
   (retract ?eval)
) ; defrule preflop-tier1

(defrule preflop-tier2 "Determine whether this pocket hand is a tier 2 hand"
   ?eval <- (preflopeval FALSE)

   (or (and (pocketpair ?v1) (test (and (>= ?v1 10) (< ?v1 ?*K*))))                             ; medium pocket pair (q, j, 10): value >= 10, but not A-K (tier 1)

       (suited ?v1&?*A* ?v2)                                                                    ; suited with ace (ace-first condition)
       (suited ?v1 ?v2&?*A*)                                                                    ; suited with ace (kicker-first condition)

       (and (conn ?v1 ?v2) (test (= (+ ?v1 ?v2) (+ ?*A* ?*K*))))                                ; ace-king (not suited)

       (and (suitedconn ?v1 ?v2) (test (and (> (+ ?v1 ?v2) 20) (< (+ ?v1 ?v2) (+ ?*A* ?*K*))))) ; suited connectors greater than j-10 (sum=21) but not A-K
   )
=>
   (assert (tier 2))
   (retract ?eval)
   (assert (preflopeval TRUE))
) ; defrule preflop-tier2

(defrule preflop-tier3 "Determine whether this pocket hand is a tier 3 hand"
   ?eval <- (preflopeval FALSE)

   (or (pocket ?v1&?*A* ?s1 ?v2&~?*A*&~?*K* ?s2)                                     ; first card is an A (but second card is neither A nor K)
       (pocket ?v1&~?*K*&~?*A* ?s1 ?v2&?*A* ?s2)                                     ; second card is an A (but first card is neither A nor K)

       (and (suitedconn ?v1 ?v2) (test (and (> (+ ?v1 ?v2) 10) (< (+ ?v1 ?v2) 20)))) ; checks for suited connectors, at least 5-6 (5+6=11>10), max 9-10 (9+10 < 20)

       (and (conn ?v1 ?v2) (test (and (> (+ ?v1 ?v2) 20) (< (+ ?v1 ?v2) 27))))       ; check for connectors, at least J-10(11+10 > 20), but less than (A+K = 27)
       (and (conn ?v1 ?v2) (test (= (+ ?v1 ?v2) 16)))                                ; the A-2 connector is a special case (unique sum = 16) that falls into tier 3

       (and (pocketpair ?v1) (test (and (> ?v1 6) (<= ?v1 9))))                      ; pocket pairs at least 6-6, but maximum 9-9

       (and (suited ?v1&~?*A* ?v2&~?*A*) (test (>= (+ ?v1 ?v2) 16)))                 ; any suited hand with sum value > 16, but no aces allowed 
   ) ; or (pocket ?v1&?*A* ?s1 ?v2&~?*A*&~?*K* ?s2)    
=>
   (assert (tier 3))
   (retract ?eval)
   (assert (preflopeval TRUE)) 
) ; defrule preflop-tier3

(defrule preflop-tier4 "Determine whether this pocket hand is a tier 4 hand"
   ?eval <- (preflopeval FALSE)

   (or (and (suitedconn ?v1 ?v2) (test (< (+ ?v1 ?v2) 10)))                                ; any suited connectors hand less than a 5-6

       (and (conn ?v1&~?*A* ?v2&~?*A*) (test (and (> (+ ?v1 ?v2) 12) (< (+ ?v1 ?v2) 20)))) ; check for decent connectors, at least 6-7, less than J-10

       (and (pocketpair ?v1) (test (<= ?v1 6)))                                            ; any pocket pair less than 6-6

       (and (suited ?v1&~?*A* ?v2&~?*A*) (test (< (+ ?v1 ?v2) 16)))                        ; any suited hand that has a sum value < 16

       (and (pocket ?v1&~?*A* ?s1 ?v2&~?v1&~?*A* ?s2&~?s1) (test (> (+ ?v1 ?v2) 20)))      ; non-suited, non-connector decent hand: sum greater than 20
   )
=>
   (assert (tier 4))
   (retract ?eval)
   (assert (preflopeval TRUE))    
) ; defrule preflop-tier4

/*
* Tier 5 is the catch-all, worst tier for pocket hands that are not tier 1, 2, 3, or 4:
* because it is too hard to try to represent this class explicitly, instead a low-salience rule is used that will be called
* if no other tier value has been asserted to assert (tier 5).
*/

(defrule preflop-tier5 "Check whether this pocket hand is just a tier 5 hand"
   (declare (salience -1))      ; ensures that this rule will be checked last out of the tier rules, only if needed
   ?eval <- (preflopeval FALSE) ; this rule should not fire once another tier has been selected (preflopeval TRUE)
=>
   (assert (tier 5))
   (retract ?eval)
   (assert (preflopeval TRUE)) 
) ; defrule preflop-tier5

/**
* Preflop decision making rules: using tier and other condition information, suggest a move
* Constants used throughout (like 2, 4, 8, 16 for comparison of chip stack size to preflop bet, and 10*big blind for tier 1 raising)
* are general rule-of-thumb thresholds derived from interview notes, which are explained at the top of the file in the declaration of the constants.
**/

/*
* RAISE preflop rules
*/

(defrule preflop-raise-tier1-allin "Raise all-in if tier 1 and preflop bet at least half of stack size"
   ?stage <- (preflopdone FALSE)
   (tier 1)

   (stacksize ?s) (betpreflop ?bpf) (test (and (< ?bpf ?s) (>= (* ?*CRITICALMONEY* ?bpf) ?s))) ; note: stack size greater than bet to be able to raise
=>
   ; if you have less than double of what already been bet, go all in
   (printout t "You should raise and go all in -- put in all " ?s "! " crlf)
   (printout t "This may seem like a risky play, which in a sense it is, but it is definitely worth it: your hand is really great." crlf)
   (printout t "Raising early will push out people to minimize the number who can challenge you later in the game, so you're likely to win." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-raise-tier1-allin

(defrule preflop-raise-tier1-portionin "Raise if tier 1 but at least double the preflop bet in stack size"
   ?stage <- (preflopdone FALSE)
   (tier 1)

   (stacksize ?s) (betpreflop ?bpf) (bigblind ?bb) (test (< (* ?*CRITICALMONEY* ?bpf) ?s))
=>
   (bind ?betamt (min (max ?bpf (* ?*BIGBLIND_LARGERAISE* ?bb)) (- ?s ?bpf))) ; raise by bet amount or 10*bigblind (the higher one), but ensure max is (stacksize-bet)
   
   (printout t "You should raise, by " ?betamt "! " crlf)
   (printout t "Your hand is really great. " )
   (printout t "Raising early will push out people to minimize the number who can challenge you later in the game, so you're likely to win." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-raise-tier1-portionin

(defrule preflop-raise-tier2-money "Raise if tier 2 and have quite a bit of money compared to preflop bet"
   ?stage <- (preflopdone FALSE)
   (tier 2)

   (position ?p&~?*GUN*&~?*AFTERGUN*) 
   (bigblind ?bb) (stacksize ?s) (betpreflop ?bpf) (test (< (* ?*GOODMONEY* ?bpf) ?s))
=>
   (bind ?betamt (min (max (* ?*LOWMONEY* ?bpf) (* ?*BIGBLIND_MEDRAISE* ?bb)) (- ?s ?bpf))) ; like in tier1-portionin rule, ensure max raise is (stacksize-bet)

   (printout t "You should raise, by " ?betamt " (or more, if you can and you're feeling aggressive!). " crlf)
   (printout t "Your hand is quite good. You have plenty of chips to justify this bet, so raising early isn't a big risk and helps push out the competition." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-raise-tier2-money

(defrule preflop-raise-tier2-position "Raise if tier 2 and have decent money and in good position"
   ?stage <- (preflopdone FALSE)
   (tier 2)

   (stacksize ?s) (betpreflop ?bpf) (bigblind ?bb) (test (<= (* ?*LOWMONEY* ?bpf) ?s)) 
   (position ?p) (test (< ?p ?*GUN*)) ; position of 1 and 2 is in the blinds, which is strong
=>
   (bind ?betamt (min (max ?bpf (* ?*BIGBLIND_MEDRAISE* ?bb)) (- ?s ?bpf))) ; like in tier1-portionin rule

   (printout t "You should raise, by " ?betamt " (or more, if you can and you're feeling aggressive!). " crlf)
   (printout t "Your hand is quite good. You're also in the blinds, which is a strong position to play from preflop," crlf)
   (printout t "so raising early isn't a big risk and helps push out the competition." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-raise-tier2-position

(defrule preflop-raise-tier3-takeDownLimpers "Raise if tier 3, in the big blind, and no one has raised you"
   ?stage <- (preflopdone FALSE)
   (tier 3)

   (betpreflop ?bpf&0) 
   (position ?p&?*BIG_BLIND*) 
=>
   (printout t "It might be a good idea to raise here (by a small amount upto your discretion). " crlf)
   (printout t "Your hand is decent, and you're in the big blind. " crlf)
   (printout t "But since no one has raised you, it looks like people might just be 'limping in,' so an early raise might get many to fold." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-raise-tier3-takeDownLimpers

/*
* CALL preflop rules
*/

(defrule preflop-call-tier1-allin "Call large preflopbet by going all in if tier 1"
   ?stage <- (preflopdone FALSE)
   (tier 1)

   (betpreflop ?bpf) (stacksize ?s) (test (>= ?bpf ?s))
=>
   (printout t "You should go all in to stay in the game! Your hand is really great -- it isn't going to get much better than this. " crlf)
   (printout t "So, even though this is a risky play, this is one of those situations which warrants going all in." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier1-allin

(defrule preflop-call-tier2-badposition "Call if tier 2 but not in a great position"
   ?stage <- (preflopdone FALSE)
   (tier 2)

   (position ?p) (test (or (= ?p ?*GUN*) (= ?p ?*AFTERGUN*)))
   (stacksize ?s) (betpreflop ?bpf&~0) (test (>= ?s (* ?*LOWMONEY* ?bpf)))
=>
   (printout t "You should call the bet here." crlf)
   (printout t "Your cards are quite good, but you're not in a good position." crlf)
   (printout t "Still, your stack size isn't critically low, so you can still make this call." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier2-badposition

(defrule preflop-call-tier2-badmoney "Call if tier 2 but don't have a lot of money compared to preflop bet"
   ?stage <- (preflopdone FALSE)
   (tier 2)

   (stacksize ?s) (betpreflop ?bpf&~0) (test (and (> (* ?*LOWMONEY* ?bpf) ?s) (<= (* ?*CRITICALMONEY* ?bpf) ?s)))
=>
   (printout t "You should call the bet here." crlf)
   (printout t "Your cards are quite good, but you don't really have much money compared to the bet that was just made." crlf)
   (printout t "While you shouldn't raise, your cards are definitely good enough to justify calling rather than folding." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier2-badmoney

(defrule preflop-call-tier3-decentconditions "Call if tier 3 and have decent money and in decent position"
   ?stage <- (preflopdone FALSE)
   (tier 3)

   (position ?p&~?*GUN*) 
   (stacksize ?s) (betpreflop ?bpf&~0) (test (> ?s (* ?*GOODMONEY* ?bpf)))
=>
   (printout t "You should call the bet here." crlf)
   (printout t "Your cards are decent, your position seems fine, and you have a good amount of money to sustain this bet." crlf)
   (printout t "You can fold if you want to be extra cautious, but calling is probably a good idea." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier3-decentconditions

(defrule preflop-call-tier3-greatmoney "Call if tier 3 and have lots of money, even in bad position"
   ?stage <- (preflopdone FALSE)
   (tier 3)

   (position ?p&?*GUN*) 
   (stacksize ?s) (betpreflop ?bpf&~0) (test (> ?s (* ?*HIGHMONEY* ?bpf)))
=>
   (printout t "You can probably call here." crlf)
   (printout t "Your cards are decent, and your position is weak, but you have plenty of money to sustain this bet." crlf)
   (printout t "You can fold if you want to be extra cautious, but calling is probably a good idea." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier3-greatmoney

(defrule preflop-call-tier4-goodmoneyposition "Call if tier 4 and have good money and in fine position"
   ?stage <- (preflopdone FALSE)
   (tier 4)

   (position ?p) (test (or (< ?p ?*GUN*) (> ?p ?*AFTERGUN*)))               
   (stacksize ?s) (betpreflop ?bpf&~0) (test (> ?s (* ?*HIGHMONEY* ?bpf))) 
=>
   (printout t "Even though your cards aren't really good, you should probably call here." crlf)
   (printout t "You're definitely not in a weak position, and you have plenty of money to sustain this bet." crlf)
   (printout t "Fold if you want to play tight or cautious, but otherwise you should call here." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier4-goodmoneyposition

(defrule preflop-call-tier5-free "Check to call with tier 5"
   ?stage <- (preflopdone FALSE)
   (tier 5)

   (betpreflop ?bpf&0)
=>
   (printout t "Well, your pocket cards are pretty terrible, ")
   (printout t "but given that it's no additional cost to you to stay in the game, you might as well call (or check, in this case)!" crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier5-free

(defrule preflop-call-tier4-free "Check to call with tier 4"
   ?stage <- (preflopdone FALSE)
   (tier 4)

   (betpreflop ?bpf&0)
=>
   (printout t "Well, your pocket cards aren't really good, ")
   (printout t "but given that it's no additional cost to you to stay in the game, you might as well call (or check, in this case)!" crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier4-free

(defrule preflop-call-tier3-free "Check to call with tier 3"
   ?stage <- (preflopdone FALSE)
   (tier 3)

   (betpreflop ?bpf&0) (position ?p&~?*BIG_BLIND*)
=>
   (printout t "Well, your pocket cards are decent, ")
   (printout t "but given that it's no additional cost to you to stay in the game, you might as well call (or check, in this case)!" crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier3-free

(defrule preflop-call-tier2-badpositionfree "Check to call with tier 2, if in bad position (explicit rule)"
   ?stage <- (preflopdone FALSE)
   (tier 2)

   (betpreflop ?bpf&0) (position ?p) (test (or (= ?p ?*GUN*) (= ?p ?*AFTERGUN*)))
=>
   (printout t "Your pocket cards are quite good, but you're not in a great position." crlf)
   (printout t "However, given that it's no additional cost to you to stay in the game, you should definitely call (check, here) but probably not raise." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-call-tier2-badpositionfree

/*
* FOLD preflop rules
*/

(defrule preflop-fold-tier5 "Fold if tier 5 and non-zero bet made"
   ?stage <- (preflopdone FALSE)
   (tier 5)

   (betpreflop ?bpf&~0)
=>
   (printout t "You should fold." crlf)
   (printout t "From what I can see, your pocket cards are pretty terrible, so you really don't want to call the bet in order to play them." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-fold-tier5

(defrule preflop-fold-tier4-badposition "Fold if tier 4 in bad position and non-zero bet made"
   ?stage <- (preflopdone FALSE)
   (tier 4)

   (betpreflop ?bpf&~0)
   (position ?p) (test (or (= ?p ?*GUN*) (= ?p ?*AFTERGUN*)))
=>
   (printout t "You should fold." crlf)
   (printout t "Your pocket cards really aren't great. " crlf
    "On top of that you have to play early, so your positioning makes you even weaker." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-fold-tier4-badposition

(defrule preflop-fold-tier4-badmoney "Fold if tier 4 if lacking lots of money to sustain bet"
   ?stage <- (preflopdone FALSE)
   (tier 4) 

   (position ?p&~?*GUN*&~?*AFTERGUN*) 
   (stacksize ?s) (betpreflop ?bpf) (test (> (* ?*GOODMONEY* ?bpf) ?s))
=>
   (printout t "You should fold." crlf)
   (printout t "Your pocket cards really aren't great. " crlf
    "On top of that, you'd have to put in a decent portion of your total stack size to call, so it's not a great idea to call, and much less raise." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-fold-tier4-badmoney

(defrule preflop-fold-tier3-badmoneyposition "Fold if tier 3 if in bad position and lacking lots of money to sustain bet"
   ?stage <- (preflopdone FALSE)
   (tier 3)

   (position ?p&?*GUN*) 
   (stacksize ?s) (betpreflop ?bpf) (test (> (* ?*GOODMONEY* ?bpf) ?s))
=>
   (printout t "You should fold." crlf)
   (printout t "Your pocket cards are decent. "
    "However, note that you have to play early, so your positioning makes you weak. " crlf
    "You'd also have to put in a significant portion of your total stack size to call, so it's not a great idea to call, and much less raise." crlf crlf)
   
   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-fold-tier3-badmoneyposition

(defrule preflop-fold-tier3-moneydanger "Fold in tier 3 if quite low on money compared to bet made"
   ?stage <- (preflopdone FALSE)
   (tier 3)

   (stacksize ?s) (betpreflop ?bpf) (test (> (* ?*LOWMONEY* ?bpf) ?s))
=>
   (printout t "You should probably fold here." crlf)
   (printout t "Your cards are decent, but you don't have enough money to make calling that bet with only decent cards a safe play." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-fold-tier3-moneydanger

(defrule preflop-fold-tier2-moneydanger "Fold in tier 2 if extremely low on money compared to bet made"
   ?stage <- (preflopdone FALSE)
   (tier 2)

   (stacksize ?s) (betpreflop ?bpf) (test (> (* ?*CRITICALMONEY* ?bpf) ?s))
=>
   (printout t "You should probably fold here." crlf)
   (printout t "Even though your cards really are quite good, that bet is really high compared to your stack size." crlf)
   (printout t "So if you want to really play risky or suspect a bluff, you can call this bet, but the safest play would probably be to fold this time." crlf crlf)

   (retract ?stage)
   (assert (preflopdone TRUE))
   (endgame)
) ; defrule preflop-fold-tier2-moneydanger


/**
* Pocket card (preflop) evaluation rules
**/


(defrule check-pair "Check for a pocket pair"
   ?state <- (pocketpairstate FALSE)

   (Card (val ?v1) (suit ?s1))
   (Card (val ?v1) (suit ?s2 & ~?s1)) ; checks that there exists a second card with the same value, but a different suit -- thus a pair
                                      ; this style of checking for value (in)equality and suit (in)equality is repeated in other rules as well
=>
   (printout t "You have a pocket pair of " (upcase ?v1) "s!" crlf crlf)
   (retract ?state)
   (assert (pocketpair (num ?v1))) 
) ; defrule check-pair

(defrule check-suitedconnectors "Check for suited cards (but not connected)"
   ?state <- (suitedconnstate FALSE)

   (Card (val ?v1) (suit ?s1))
   (Card (val ?v2) (suit ?s1))
   (test (or (= (abs (- (num ?v1) (num ?v2))) 1) (= (abs (- (num ?v1) (num ?v2))) ?*A2DIST* ))) ; either difference is 1 (adjacent), or A-2 adjacency
=>
   (printout t "You have suited connectors!" crlf crlf)
   (retract ?state)
   (assert (suitedconn (num ?v1) (num ?v2))) 
) ; defrule check-suitedconnectors

(defrule check-connectors "Check for connectors (but not suited)"
   ?state <- (connstate FALSE)

   (Card (val ?v1) (suit ?s1))
   (Card (val ?v2) (suit ?s2&~?s1))                                                             ; make sure cards not suited (otherwise should go in suited connectors)
   (test (or (= (abs (- (num ?v1) (num ?v2))) 1) (= (abs (- (num ?v1) (num ?v2))) ?*A2DIST* ))) ; either difference is 1 (adjacent), or  A-2 adjacency (A=14, 2=2)
=>
   (printout t "You have connectors!" crlf crlf)
   (retract ?state)
   (assert (conn (num ?v1) (num ?v2))) 
) ; check-connectors

(defrule check-suited "Check for same suit (but not adjacent/connected)"
   ?state <- (suitedstate FALSE)

   (Card (val ?v1) (suit ?s1))
   (Card (val ?v2 &~?v1) (suit ?s1))                                                                  ; check that same card isn't being used twice (diff val needed)
   (test (not (or (= (abs (- (num ?v1) (num ?v2))) 1) (= (abs (- (num ?v1) (num ?v2))) ?*A2DIST* )))) ; check that cards are not connectors
=>
   (printout t "You have suited cards!" crlf crlf)
   (retract ?state)
   (assert (suited (num ?v1) (num ?v2))) 
) ; check-suited

(defrule assert-pocket "Assert a general fact about the pocket hand if not suited, connector, or pair"
   ?state <- (pocketstate FALSE)

   (Card (val ?v1) (suit ?s1))
   (Card (val ?v2&~?v1) (suit ?s2&~?s1))                                                             ; ensure not a pair, suited, or the same cards
   (test (not (or (= (abs (- (num ?v1) (num ?v2))) 1) (= (abs (- (num ?v1) (num ?v2))) ?*A2DIST*)))) ; check that cards are not connectors
   (test (not (and (= (num ?v1) (num ?v2)) (= ?s1 ?s2))))                                            ; make sure this rule is finding the two different cards
=>
   (retract ?state)
   (assert (pocket (num ?v1) ?s1 (num ?v2) ?s2))
) ; assert-pocket

/*
* Hand (postflop, turn, river) evaluation rules
*/

/*
* Utility function to convert all "value" slot values into numbers, where j = 11, q = 12, k = 13, a = 14 (and 2...10 are not changed)
* Precondition: ?v is a valid card value (has passed through validCard verification process)
*/
(deffunction num (?v)
   (if (eq ?v j) then (bind ?ret ?*J*)
    elif (eq ?v q) then (bind ?ret ?*Q*)
    elif (eq ?v k) then (bind ?ret ?*K*)
    elif (eq ?v a) then (bind ?ret ?*A*)
    else (bind ?ret ?v) ; just the same value if already a number from 2...10
   )

   (return ?ret)
) ; deffunction num (?v)


/**
* Input and validation function(s)
**/

/*
* Checks the inputted values for a card, returning a boolean that represents whether the inputted data is valid for a card or not.
* ?v is the face value of the card (2 ... 10, J, Q, K, A), and ?s is the suit of the card (C, D, H, S = clubs, diamonds, hearts, and spades)
* the boolean ?retv determines whether the value is valid, and ?rets determines whether the suit is valid
*/
(deffunction validCard (?card)
   (bind ?carditems (explode$ ?card))

   (if (= (length$ ?carditems) 2) then ; there should only be 2 items in the list (created from string): the value and the suit

      (bind ?v (lowcase (nth$ 1 ?carditems)))
      (bind ?s (lowcase (nth$ 2 ?carditems)))

      (bind ?ascv (asc ?v)) ; find ascii values to check for integers between 2 and 9: (asc 2) is 50, (asc 9) is 57
      
      (if (or (eq ?v j) (eq ?v q) (eq ?v k) (eq ?v a)) then (bind ?retv TRUE)                                ; the card value can be J, Q, K, or A
       elif (or (eq ?v "10") (and (= (str-length ?v) 1) (<= ?ascv 57) (>= ?ascv 50))) then (bind ?retv TRUE) ; check "10" or ascii for 1-digit numbers (2-9)
       else (bind ?retv FALSE)
      )

      (if (or (eq ?s c) (eq ?s d) (eq ?s h) (eq ?s s)) then (bind ?rets TRUE)
       else (bind ?rets FALSE)
      )

      (bind ?ret (and ?retv ?rets)) ; both ?retv and ?rets must be true for this to be a valid card
      
    else (bind ?ret FALSE)          ; return value should be FALSE if input string does not have two space-separated items

   ) ; if (= (length$ ?carditems) 2)
   
   (return ?ret)
) ; deffunction validCard (?card)

/**
* Startup and ending / termination rules and functions
**/

(defrule startup "Startup rule fires when this expert system is run to explain game and assert initial facts"
=>
   (printout t crlf "------------[[EXPOKER: BEGIN]]------------" crlf crlf
    "Welcome to expoker, a poker expert system that can make those hard game choices for you." crlf
    "This way, you can blame any losing decisions on artificial intelligence..." crlf
    "That's a joke, don't worry. I'll help you win." crlf crlf
   )

   (printout t "Some notes on formatting and conventions:" crlf
    "1. Cards: card values should be 2, 3, 4,...,10, J, Q, K, A; suits should be represented C, D, H, S. " crlf
    "   A card should be a value and a suit, separated by a space. Note: double values for input (e.g. 2.0 instead of 2) will not be accepted." crlf
    "2. Numbers: when numeral values are required, please input only positive integers, upto the Jess integer limit. Multiple values should be space-separated." crlf
    "3. The number of players must be at least 3 (only supports games of 3 or more) and an integer. All other values will be rejected." crlf
    "   Your position must be an integer between 1 and this value." crlf 
   )

   ; assert facts about the type of pocket hand (all FALSE right now, to be updated later), used to avoid repetitive firing
   (assert (pocketpairstate FALSE))
   (assert (suitedconnstate FALSE))
   (assert (suitedstate FALSE))
   (assert (connstate FALSE))
   (assert (pocketstate FALSE))

   ; assert fact about preflop evaluation and decision made, to be updated and monitored later
   (assert (preflopeval FALSE))
   (assert (preflopdone FALSE))

) ; defrule startup

(defrule earlyexit "Catch-all, low-salience rule for situations where system cannot figure out what the right play is"
   (declare (salience -10))
   (preflopeval TRUE)
   (preflopdone FALSE)
=>
   (assert (preflopdone TRUE))
   (printout t crlf "Well, this situation seems like a bit of a toss-up between calling and folding, so I'm really not sure what to do." crlf
    "If you want to playing aggressive, you can call and stay in the game. Otherwise, fold if you want to be extra cautious and safe." crlf crlf
   )

   (halt)
) ; defrule earlyexit

/*
* Halt the expert system from firing any additional rules or asking any additional questions when called.
*/
(deffunction endgame ()
   (printout t "Well, I hope this advice helped you out -- and I hope you followed it!" crlf)
   (halt)

   (return nil) ; nothing to return
); deffunction endgame ()

/*
* Run the game in its entirety, rerunning the expert system every time the user request to continue usage. 
*/
(deffunction play ()
   (bind ?end FALSE)

   (while (not ?end)
      (reset)
      (run)

      (bind ?end (exitgame))
   )
   
   (printout t "Thanks for playing!" crlf)

   (return nil) ; nothing to return
) ; deffunction play ()

/*
* Exit function checks whether user has asked to exit.
* Returns TRUE is user wishes to exit (input is anything that doesn't start with a "y"), FALSE if user wishes to continue (input starts with "y")
*/
(deffunction exitgame ()
   (bind ?inp (ask "Run again? Type anything that starts with a 'y' for yes, or anything else for no. "))

   (if (= (str-length ?inp) 0) then (bind ?val TRUE)
    else 
      (bind ?firstletter (sub-string 1 1 (lowcase ?inp))) ; convert to lowercase to check, as case doesn't matter

      (if (eq* ?firstletter "y") then (bind ?val FALSE)
       else (bind ?val TRUE)
      )
   )
   
   (return ?val)
) ; deffunction exitgame ()

; start the game immediately when this file is batched
(play)

