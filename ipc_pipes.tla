---- MODULE ipc_pipes ----
EXTENDS Integers, Sequences

VARIABLES buffer, reader, writer, readMutex, writeMutex

CONSTANTS BufferSize, MaxIterations

(*--algorithm PipeExample
variables buffer = <<1, 2, 3, 4, 5>>,
          reader = 0,
          writer = 0,
          item = 0;

        
define
  BufferEmpty == Len(buffer) = 0
  BufferFull == Len(buffer) = BufferSize
  CanRead == Len(buffer) > 0
  CanWrite == Len(buffer) < BufferSize
    
  BufferSize == 5
  MaxIterations == 10
end define;


process Reader = 1
variable readMutex = FALSE;
begin
  read_loop:
  while TRUE
  do
    with mutex = readMutex
    do
      await(mutex = FALSE /\ CanRead);
      readMutex := TRUE;
      item := Head(buffer);
      buffer := Tail(buffer);
      reader := (reader + 1) % BufferSize;
      \* Introduce random delay
      await Skip;
    end with;
    finish_read:
    readMutex := FALSE;
  end while;
end process;

process Writer = 2
variable writeMutex = FALSE, value = 0;
begin
  write_loop:
  while TRUE
  do
    with mutex = writeMutex
    do
      await(mutex = FALSE /\ CanWrite);
      writeMutex := TRUE;
      value := RandomElement({1, 2, 3, 4, 5});
      buffer := Append(buffer, value);
      writer := (writer + 1) % BufferSize;
      \* Introduce random delay
      await Skip;
    end with;
    finish_write:
    writeMutex := FALSE;
  end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3a553612" /\ chksum(tla) = "9656028a")
VARIABLES buffer, reader, writer, item, pc

(* define statement *)
BufferEmpty == Len(buffer) = 0
BufferFull == Len(buffer) = BufferSize
CanRead == Len(buffer) > 0
CanWrite == Len(buffer) < BufferSize

BufferSize == 5
MaxIterations == 10

VARIABLES readMutex, writeMutex, value

vars == << buffer, reader, writer, item, pc, readMutex, writeMutex, value >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ buffer = <<1, 2, 3, 4, 5>>
        /\ reader = 0
        /\ writer = 0
        /\ item = 0
        (* Process Reader *)
        /\ readMutex = FALSE
        (* Process Writer *)
        /\ writeMutex = FALSE
        /\ value = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "read_loop"
                                        [] self = 2 -> "write_loop"]

read_loop == /\ pc[1] = "read_loop"
             /\ LET mutex == readMutex IN
                  /\ (mutex = FALSE /\ CanRead)
                  /\ readMutex' = TRUE
                  /\ item' = Head(buffer)
                  /\ buffer' = Tail(buffer)
                  /\ reader' = (reader + 1) % BufferSize
                  /\ Skip
             /\ pc' = [pc EXCEPT ![1] = "finish_read"]
             /\ UNCHANGED << writer, writeMutex, value >>

finish_read == /\ pc[1] = "finish_read"
               /\ readMutex' = FALSE
               /\ pc' = [pc EXCEPT ![1] = "read_loop"]
               /\ UNCHANGED << buffer, reader, writer, item, writeMutex, value >>

Reader == read_loop \/ finish_read

write_loop == /\ pc[2] = "write_loop"
              /\ LET mutex == writeMutex IN
                   /\ (mutex = FALSE /\ CanWrite)
                   /\ writeMutex' = TRUE
                   /\ value' = RandomElement({1, 2, 3, 4, 5})
                   /\ buffer' = Append(buffer, value')
                   /\ writer' = (writer + 1) % BufferSize
                   /\ Skip
              /\ pc' = [pc EXCEPT ![2] = "finish_write"]
              /\ UNCHANGED << reader, item, readMutex >>

finish_write == /\ pc[2] = "finish_write"
                /\ writeMutex' = FALSE
                /\ pc' = [pc EXCEPT ![2] = "write_loop"]
                /\ UNCHANGED << buffer, reader, writer, item, readMutex, value >>

Writer == write_loop \/ finish_write

Next == Reader \/ Writer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
