----------------------------- MODULE ipc_pipes -----------------------------
EXTENDS Integers, Sequences

(* --algorithm ipc_pipes


variables buffer = <<>>, reader = 0, writer = 0

define
    MaxIterations == 10
    BufferSize == 5
    BufferEmpty == Len(buffer) = 0
    BufferFull == Len(buffer) = BufferSize
    CanRead == Len(buffer) > 0
    CanWrite == Len(buffer) < BufferSize

end define;

fair process Reader = 1
    variables item, i = 0;
    
    begin
       Read:
        while (i =< Maxiterations) do
            if (CanRead) then
                item := Head(buffer);
                buffer := Tail(buffer);
                reader := (reader + 1) % BufferSize;
                i := i + 1;
            end if
        end while;
    end process;

fair process Writer = 2
    variable value, i = 0;
    begin
        Write:
        while (i =< Maxiterations) do
            if (CanWrite)  then
                buffer := Append(buffer, value);
                writer := (writer + 1) % BufferSize;
                i := i + 1;
            end if;
        end while;
    end process;

end algorithm;

\* Safety Property: Buffer OK
\* Buffer not overflown
Invariant "Buffer OK":
    Len(buffer) <= BufferSize

\* Safety Property: Reader-Writer Exclusion
\* The reader and writer should not access the buffer at the same time.
Invariant "Reader-Writer Exclusion":
    \A i, j \in 1..Len(buffer) :
        i # j => (reader % BufferSize = i - 1) \/ (writer % BufferSize = i - 1)

\* Liveness Property: Reader Progress
\* If there is data in the buffer, the reader should eventually read it.
Fairness "Reader Progress":
    \A i \in 1..MaxIterations :
        CanRead => (WF_vars <<item>> : Read)

\* Liveness Property: Writer Progress
\* If there is space in the buffer, the writer should eventually write to it.
Fairness "Writer Progress":
    \A i \in 1..MaxIterations :
        CanWrite => (WF_vars <<value>> : Write(value)

*)
\* BEGIN TRANSLATION (chksum(pcal) = "3243781e" /\ chksum(tla) = "418fb04d")
\* Process variable i of process Reader at line 20 col 21 changed to i_
CONSTANT defaultInitValue
VARIABLES buffer, reader, writer, pc

(* define statement *)
MaxIterations == 10
BufferSize == 5
BufferEmpty == Len(buffer) = 0
BufferFull == Len(buffer) = BufferSize
CanRead == Len(buffer) > 0
CanWrite == Len(buffer) < BufferSize

VARIABLES item, i_, value, i

vars == << buffer, reader, writer, pc, item, i_, value, i >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ buffer = <<>>
        /\ reader = 0
        /\ writer = 0
        (* Process Reader *)
        /\ item = defaultInitValue
        /\ i_ = 0
        (* Process Writer *)
        /\ value = defaultInitValue
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Read"
                                        [] self = 2 -> "Write"]

Read == /\ pc[1] = "Read"
        /\ IF (i_ =< 10)
              THEN /\ IF (CanRead)
                         THEN /\ item' = Head(buffer)
                              /\ buffer' = Tail(buffer)
                              /\ reader' = (reader + 1) % BufferSize
                              /\ i_' = i_ + 1
                         ELSE /\ TRUE
                              /\ UNCHANGED << buffer, reader, item, i_ >>
                   /\ pc' = [pc EXCEPT ![1] = "Read"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                   /\ UNCHANGED << buffer, reader, item, i_ >>
        /\ UNCHANGED << writer, value, i >>

Reader == Read

Write == /\ pc[2] = "Write"
         /\ IF (i =< 10)
               THEN /\ IF (CanWrite)
                          THEN /\ buffer' = Append(buffer, value)
                               /\ writer' = (writer + 1) % BufferSize
                               /\ i' = i + 1
                          ELSE /\ TRUE
                               /\ UNCHANGED << buffer, writer, i >>
                    /\ pc' = [pc EXCEPT ![2] = "Write"]
               ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
                    /\ UNCHANGED << buffer, writer, i >>
         /\ UNCHANGED << reader, item, i_, value >>

Writer == Write

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Reader \/ Writer
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Reader)
        /\ WF_vars(Writer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
