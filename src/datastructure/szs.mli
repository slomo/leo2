type status =
    SUC
  | UNP
  | SAP
  | ESA
  | SAT
  | FSA
  | THM
  | EQV
  | TAC
  | WEC
  | ETH
  | TAU
  | WTC
  | WTH
  | CAX
  | SCA
  | TCA
  | WCA
  | CUP
  | CSP
  | ECS
  | CSA
  | CTH
  | CEQ
  | UNC
  | WCC
  | ECT
  | FUN
  | UNS
  | WUC
  | WCT
  | SCC
  | UCA
  | NOC
  | NOS
  | OPN
  | UNK
  | ASS
  | STP
  | ERR
  | OSE
  | INE
  | SYE
  | SEE
  | TYE
  | FOR
  | USR
  | RSO
  | TMO
  | MMO
  | GUP
  | INC
  | IAP
  | INP
  | NTT
  | NTY
exception InvalidSzsStatus of string
val status_strings : (status * (string * string)) list
val relation : (status * status list) list
val string_of_szs : status -> string
val read_status : string -> status option
val is_a : status -> status -> bool
