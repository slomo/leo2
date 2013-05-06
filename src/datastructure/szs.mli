type szs_status =
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
val szs_status_strings : (szs_status * (string * string)) list
val szs_relation : (szs_status * szs_status list) list
val szs_read_status : string -> szs_status
val szs_is_a : szs_status -> szs_status -> bool
