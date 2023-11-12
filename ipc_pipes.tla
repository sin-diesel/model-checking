---- MODULE ipc_pipes ----

EXTENDS Sequences, Integers

VARIABLES
    \* @type: Str
    pipe_status,
    \* @type: Seq(Str)
    pipe,
    \* @type: Int
    pipe_size,
    \* @type: Str
    reader_status,
    \* @type: Str
    writer_status

Init ==
    /\ pipe_status = "UNCREATED"
    /\ pipe = <<>>
    /\ pipe_size = 0
    /\ reader_status = "UNREAD"
    /\ writer_status = "UNWRITE"

CreatePipe ==
    /\ pipe_status = "CREATED"
    /\ UNCHANGED <<pipe, reader_status, writer_status>>

ReadFromPipe(m) ==
    /\ m \in pipe
    /\ pipe_status = "ISREAD"
    /\ pipe' = pipe - m
    /\ pipe_size' = pipe_size - 1
    /\ reader_status = "READ"
    /\ UNCHANGED <<writer_status>>

WriteToPipe(m) ==
    /\ pipe_status = "WRITTEN"
    /\ pipe' = pipe + m
    /\ pipe_size' = pipe_size + 1
    /\ writer_status' = "WRITE"
    /\ UNCHANGED <<reader_status>>

ClosePipe ==
    /\ pipe_status = "CLOSED"
    /\ UNCHANGED <<pipe, pipe_size, reader_status, writer_status>>

Next ==
    /\ CreatePipe
    /\ WriteToPipe("Hello world!")
    /\ ReadFromPipe("Hello world!")
    /\ ClosePipe

SafetyPipeEmpty == <>(pipe_status = "CLOSED")
====
