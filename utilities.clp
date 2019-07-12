/*
** January 18, 2019
** Dr. Eric R. Nelson
**
** Small collection of JESSS utilities for ATCS:Expert Systems
**
** print       - prints any argument
** printline   - print followed by a newline
** ask         - prompt the user and read back a token
** askline     - prompt the user and read back a line of text (a string)
** askQuestion - adds a question mark to the prompt used in ask
*/

/*
** Function that prints out a prompt (it's just a bit shorter than using (printout t "text")
*/
(deffunction print (?arg)
   (printout t ?arg)
   (return)
)

/*
** print with a new-line at the end
*/
(deffunction printline (?arg)
   (print ?arg)
   (printout t crlf)
   (return)
)

/*
** ask the user for input and return a token
*/
(deffunction ask (?arg)
   (print ?arg)
   (return (read))
)

/*
** Same as ask but returns a string of text
*/
(deffunction askline (?arg)
   (print ?arg)
   (return (readline))
)

/*
** Appends a question mark to the prompt of the ask function
*/ 
(deffunction askQuestion (?arg)
   (print ?arg)
   (return (ask "? "))
)
