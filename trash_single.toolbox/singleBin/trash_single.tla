---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];
  truckCommands = << >>,
  grantedPerm = {},
  trucking = FALSE,

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
Full == Trash + MaxUserTrash \div 2 >= trashCapacity
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed 
CapacityNotExceeded == ~CapacityExceeded


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.

\* The outer door can only be locked if it is closed.
OuterDoorLocked == [](~outerDoorLocked \/ ~outerDoorOpen)
\* The vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == [](~ramExtended \/ outerDoorLocked)
\* Every time the trash bin is full, it is eventually not full anymore.
TrashEmptied == Full ~> ~Full
\* An unauthorized user cannot open the outer door.
AuthorizedOpenOnly == \A u  \in Users : 
 (pc[u] \in {"UserOpenDoor", "UserAwaitOpenDoor", "UserDepositTrash","UserCloseDoor", "UserAwaitClosedDoor"}) => (u \in grantedPerm)

\* The user infinitely often has trash and infinitely often has no trash.
UserTrash == ([]<> (userTrash > 0)) /\ ([]<> (userTrash = 0))
\* Every time the user has trash, they can deposit their trash.
UserTrashDeposited == [](userTrash > 0 ~> userTrash = 0)
\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
TruckEmpties == truckCommands # << >> ~> Trash = 0

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro

macro waitBin() begin
await binCommand.command = "finished";
end macro;


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
  UserRemovePerm:
        grantedPerm := grantedPerm \{self};
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair  process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
        if valid then
            grantedPerm:= grantedPerm \union {req.user};
        end if;
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* DUMMY truck process type.
\* Remodel it to react to requests and empty the trash bin!
fair process truckProcess \in Trucks
variables
    command = [command |-> "idle", bin |-> 1];
begin
  TruckStart:
    \* Implement behaviour
    while TRUE do 
        ReadCommand:
        \*print("wait call");
        read(truckCommands, command);
        \* await trucking
        \* trucking:=TRUE;
        
        Execute:
        \*print("empty truck");
        waitBin();
        binCommand:=[command |-> "empty"];
        WaitBinTruck:
        waitBin();
        trucking:=FALSE;
    
    end while;
    skip;
end process;


\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control the trash bin system and handle requests by users!
fair process controlProcess = Control
variables

    scan = [user |-> 0, bin |-> 0];
    perm = [user |-> 0, permission |-> FALSE];

begin
  ControlStart:
    \* Implement behaviour
    while TRUE do
        \*if scans # <<>> then 
        \* request auth
            ReadCard:
            \*print("reading card");
            read(scans, scan);
            AskServer:
            \*print("ask srv");
            write(serverRequests, [user |-> scan.user]);
            WaitServer:
            \*print("wait srv");
            read(serverResponses, perm);
            CheckPerm: 
            \*print("checking");
            \*print(perm.permission);
            if ~perm.permission then
                ForbidUser:
                \*print("forbidden");
                write(permissions, [user |-> scan.user, granted |-> perm.permission, bin |-> scan.bin]);
                \* unauthorized, abort
                goto ControlStart;
            end if;
            AllowUser:
            \*print("open");
            binCommand := [command |-> "change_outer_lock", open |-> TRUE];
            WaitBin1:
            waitBin();
            write(permissions, [user |-> scan.user, granted |-> perm.permission, bin |-> scan.bin]);
            
            WaitDoorClosed:
            \*print("wait closed");
            await binSensor.sensor = "outer_door_closed";
            binSensor.sensor := "idle";
            
            \* lock door
            LockDoor:
            waitBin();
            \*print("lock");
            binCommand := [command |-> "change_outer_lock", open |-> FALSE];
              
            \* open trapdoor
            Trap:
            waitBin();
            \*print("drop");
            binCommand := [command |-> "change_trap_door", open |-> TRUE];
            
            \* ram
            Ram:
            waitBin();
            binCommand := [command |-> "change_ram", open |-> TRUE];
            
            \* unram
            UnRam:
            waitBin();
            binCommand:= [command |-> "change_ram", open |-> FALSE];            
            \* close trap
            UnTrap:
            waitBin();
            \*print("undrop");
            binCommand:= [command |-> "change_trap_door", open |-> FALSE];
            
            \* maybe empty
            Empty:
            waitBin();
            if Full then 
                \*print("call truck");
                write(truckCommands, [command |-> "empty", bin |-> scan.bin]);
                \* WaitT1:
                \* await trucking;
                trucking := TRUE;
                WaitT2:
                await ~trucking;
            end if;

        \*end if;
    
    end while;
    
    skip;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "436d09c6" /\ chksum(tla) = "f1a33806")
\* Process variable perm of process userProcess at line 227 col 3 changed to perm_
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, truckCommands, 
          grantedPerm, trucking, pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
Full == Trash + MaxUserTrash \div 2 >= trashCapacity
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity






TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins


MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded








OuterDoorLocked == [](~outerDoorLocked \/ ~outerDoorOpen)

RamOuterDoor == [](~ramExtended \/ outerDoorLocked)

TrashEmptied == Full ~> ~Full

AuthorizedOpenOnly == \A u  \in Users :
 (pc[u] \in {"UserOpenDoor", "UserAwaitOpenDoor", "UserDepositTrash","UserCloseDoor", "UserAwaitClosedDoor"}) => (u \in grantedPerm)


UserTrash == ([]<> (userTrash > 0)) /\ ([]<> (userTrash = 0))

UserTrashDeposited == [](userTrash > 0 ~> userTrash = 0)

TruckEmpties == truckCommands # << >> ~> Trash = 0

VARIABLES perm_, req, command, scan, perm

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, 
           truckCommands, grantedPerm, trucking, pc, perm_, req, command, 
           scan, perm >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        /\ truckCommands = << >>
        /\ grantedPerm = {}
        /\ trucking = FALSE
        (* Process userProcess *)
        /\ perm_ = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process truckProcess *)
        /\ command = [self \in Trucks |-> [command |-> "idle", bin |-> 1]]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 0]
        /\ perm = [user |-> 0, permission |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 172, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 179, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 182, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 194, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 206, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 207, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 208, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 209, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 210, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 214, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, truckCommands, 
                                           grantedPerm, trucking, perm_, req, 
                                           command, scan, perm >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, truckCommands, 
                                            grantedPerm, trucking, perm_, req, 
                                            command, scan, perm >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           truckCommands, grantedPerm, 
                                           trucking, perm_, req, command, scan, 
                                           perm >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, truckCommands, grantedPerm, 
                                      trucking, perm_, req, command, scan, 
                                      perm >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm_' = [perm_ EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm_'[self].user = self, 
                                         "Failure of assertion at line 241, column 7.")
                               /\ Assert(perm_'[self].bin = 1, 
                                         "Failure of assertion at line 242, column 7.")
                               /\ IF perm_'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, truckCommands, 
                                               grantedPerm, trucking, req, 
                                               command, scan, perm >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, truckCommands, grantedPerm, 
                                      trucking, perm_, req, command, scan, 
                                      perm >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           truckCommands, grantedPerm, 
                                           trucking, perm_, req, command, scan, 
                                           perm >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 249, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, 
                                          truckCommands, grantedPerm, trucking, 
                                          perm_, req, command, scan, perm >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, truckCommands, 
                                       grantedPerm, trucking, perm_, req, 
                                       command, scan, perm >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserRemovePerm"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             truckCommands, grantedPerm, 
                                             trucking, perm_, req, command, 
                                             scan, perm >>

UserRemovePerm(self) == /\ pc[self] = "UserRemovePerm"
                        /\ grantedPerm' = (grantedPerm \{self})
                        /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, permissions, serverRequests, 
                                        serverResponses, truckCommand, 
                                        truckCommands, trucking, perm_, req, 
                                        command, scan, perm >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, truckCommands, grantedPerm, 
                                      trucking, perm_, req, command, scan, 
                                      perm >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self)
                        \/ UserRemovePerm(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, 
                                       truckCommands, grantedPerm, trucking, 
                                       perm_, req, command, scan, perm >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           /\ serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                           /\ IF valid
                                 THEN /\ grantedPerm' = (grantedPerm \union {req'.user})
                                 ELSE /\ TRUE
                                      /\ UNCHANGED grantedPerm
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, truckCommands, 
                                      trucking, perm_, command, scan, perm >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "ReadCommand"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, truckCommands, grantedPerm, 
                                    trucking, perm_, req, command, scan, perm >>

ReadCommand(self) == /\ pc[self] = "ReadCommand"
                     /\ truckCommands /= <<>>
                     /\ command' = [command EXCEPT ![self] = Head(truckCommands)]
                     /\ truckCommands' = Tail(truckCommands)
                     /\ pc' = [pc EXCEPT ![self] = "Execute"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, grantedPerm, trucking, 
                                     perm_, req, scan, perm >>

Execute(self) == /\ pc[self] = "Execute"
                 /\ binCommand.command = "finished"
                 /\ binCommand' = [command |-> "empty"]
                 /\ pc' = [pc EXCEPT ![self] = "WaitBinTruck"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, truckCommands, grantedPerm, 
                                 trucking, perm_, req, command, scan, perm >>

WaitBinTruck(self) == /\ pc[self] = "WaitBinTruck"
                      /\ binCommand.command = "finished"
                      /\ trucking' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, 
                                      truckCommands, grantedPerm, perm_, req, 
                                      command, scan, perm >>

truckProcess(self) == TruckStart(self) \/ ReadCommand(self)
                         \/ Execute(self) \/ WaitBinTruck(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ pc' = [pc EXCEPT ![Control] = "ReadCard"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, truckCommands, 
                                grantedPerm, trucking, perm_, req, command, 
                                scan, perm >>

ReadCard == /\ pc[Control] = "ReadCard"
            /\ scans /= <<>>
            /\ scan' = Head(scans)
            /\ scans' = Tail(scans)
            /\ pc' = [pc EXCEPT ![Control] = "AskServer"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userTrash, binCommand, binSensor, permissions, 
                            serverRequests, serverResponses, truckCommand, 
                            truckCommands, grantedPerm, trucking, perm_, req, 
                            command, perm >>

AskServer == /\ pc[Control] = "AskServer"
             /\ serverRequests' = Append(serverRequests, ([user |-> scan.user]))
             /\ pc' = [pc EXCEPT ![Control] = "WaitServer"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, scans, 
                             permissions, serverResponses, truckCommand, 
                             truckCommands, grantedPerm, trucking, perm_, req, 
                             command, scan, perm >>

WaitServer == /\ pc[Control] = "WaitServer"
              /\ serverResponses /= <<>>
              /\ perm' = Head(serverResponses)
              /\ serverResponses' = Tail(serverResponses)
              /\ pc' = [pc EXCEPT ![Control] = "CheckPerm"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userTrash, binCommand, binSensor, scans, 
                              permissions, serverRequests, truckCommand, 
                              truckCommands, grantedPerm, trucking, perm_, req, 
                              command, scan >>

CheckPerm == /\ pc[Control] = "CheckPerm"
             /\ IF ~perm.permission
                   THEN /\ pc' = [pc EXCEPT ![Control] = "ForbidUser"]
                   ELSE /\ pc' = [pc EXCEPT ![Control] = "AllowUser"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, scans, 
                             permissions, serverRequests, serverResponses, 
                             truckCommand, truckCommands, grantedPerm, 
                             trucking, perm_, req, command, scan, perm >>

ForbidUser == /\ pc[Control] = "ForbidUser"
              /\ permissions' = Append(permissions, ([user |-> scan.user, granted |-> perm.permission, bin |-> scan.bin]))
              /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userTrash, binCommand, binSensor, scans, 
                              serverRequests, serverResponses, truckCommand, 
                              truckCommands, grantedPerm, trucking, perm_, req, 
                              command, scan, perm >>

AllowUser == /\ pc[Control] = "AllowUser"
             /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
             /\ pc' = [pc EXCEPT ![Control] = "WaitBin1"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binSensor, scans, permissions, 
                             serverRequests, serverResponses, truckCommand, 
                             truckCommands, grantedPerm, trucking, perm_, req, 
                             command, scan, perm >>

WaitBin1 == /\ pc[Control] = "WaitBin1"
            /\ binCommand.command = "finished"
            /\ permissions' = Append(permissions, ([user |-> scan.user, granted |-> perm.permission, bin |-> scan.bin]))
            /\ pc' = [pc EXCEPT ![Control] = "WaitDoorClosed"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userTrash, binCommand, binSensor, scans, 
                            serverRequests, serverResponses, truckCommand, 
                            truckCommands, grantedPerm, trucking, perm_, req, 
                            command, scan, perm >>

WaitDoorClosed == /\ pc[Control] = "WaitDoorClosed"
                  /\ binSensor.sensor = "outer_door_closed"
                  /\ binSensor' = [binSensor EXCEPT !.sensor = "idle"]
                  /\ pc' = [pc EXCEPT ![Control] = "LockDoor"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, scans, 
                                  permissions, serverRequests, serverResponses, 
                                  truckCommand, truckCommands, grantedPerm, 
                                  trucking, perm_, req, command, scan, perm >>

LockDoor == /\ pc[Control] = "LockDoor"
            /\ binCommand.command = "finished"
            /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
            /\ pc' = [pc EXCEPT ![Control] = "Trap"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userTrash, binSensor, scans, permissions, 
                            serverRequests, serverResponses, truckCommand, 
                            truckCommands, grantedPerm, trucking, perm_, req, 
                            command, scan, perm >>

Trap == /\ pc[Control] = "Trap"
        /\ binCommand.command = "finished"
        /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
        /\ pc' = [pc EXCEPT ![Control] = "Ram"]
        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                        ramExtended, trashInTop, trashCompressed, 
                        trashUncompressed, trashCapacity, trapDestroyed, 
                        userTrash, binSensor, scans, permissions, 
                        serverRequests, serverResponses, truckCommand, 
                        truckCommands, grantedPerm, trucking, perm_, req, 
                        command, scan, perm >>

Ram == /\ pc[Control] = "Ram"
       /\ binCommand.command = "finished"
       /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
       /\ pc' = [pc EXCEPT ![Control] = "UnRam"]
       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                       ramExtended, trashInTop, trashCompressed, 
                       trashUncompressed, trashCapacity, trapDestroyed, 
                       userTrash, binSensor, scans, permissions, 
                       serverRequests, serverResponses, truckCommand, 
                       truckCommands, grantedPerm, trucking, perm_, req, 
                       command, scan, perm >>

UnRam == /\ pc[Control] = "UnRam"
         /\ binCommand.command = "finished"
         /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
         /\ pc' = [pc EXCEPT ![Control] = "UnTrap"]
         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                         ramExtended, trashInTop, trashCompressed, 
                         trashUncompressed, trashCapacity, trapDestroyed, 
                         userTrash, binSensor, scans, permissions, 
                         serverRequests, serverResponses, truckCommand, 
                         truckCommands, grantedPerm, trucking, perm_, req, 
                         command, scan, perm >>

UnTrap == /\ pc[Control] = "UnTrap"
          /\ binCommand.command = "finished"
          /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
          /\ pc' = [pc EXCEPT ![Control] = "Empty"]
          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                          ramExtended, trashInTop, trashCompressed, 
                          trashUncompressed, trashCapacity, trapDestroyed, 
                          userTrash, binSensor, scans, permissions, 
                          serverRequests, serverResponses, truckCommand, 
                          truckCommands, grantedPerm, trucking, perm_, req, 
                          command, scan, perm >>

Empty == /\ pc[Control] = "Empty"
         /\ binCommand.command = "finished"
         /\ IF Full
               THEN /\ truckCommands' = Append(truckCommands, ([command |-> "empty", bin |-> scan.bin]))
                    /\ trucking' = TRUE
                    /\ pc' = [pc EXCEPT ![Control] = "WaitT2"]
               ELSE /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                    /\ UNCHANGED << truckCommands, trucking >>
         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                         ramExtended, trashInTop, trashCompressed, 
                         trashUncompressed, trashCapacity, trapDestroyed, 
                         userTrash, binCommand, binSensor, scans, permissions, 
                         serverRequests, serverResponses, truckCommand, 
                         grantedPerm, perm_, req, command, scan, perm >>

WaitT2 == /\ pc[Control] = "WaitT2"
          /\ ~trucking
          /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                          ramExtended, trashInTop, trashCompressed, 
                          trashUncompressed, trashCapacity, trapDestroyed, 
                          userTrash, binCommand, binSensor, scans, permissions, 
                          serverRequests, serverResponses, truckCommand, 
                          truckCommands, grantedPerm, trucking, perm_, req, 
                          command, scan, perm >>

controlProcess == ControlStart \/ ReadCard \/ AskServer \/ WaitServer
                     \/ CheckPerm \/ ForbidUser \/ AllowUser \/ WaitBin1
                     \/ WaitDoorClosed \/ LockDoor \/ Trap \/ Ram \/ UnRam
                     \/ UnTrap \/ Empty \/ WaitT2

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Oct 07 14:12:20 CEST 2026 by jerzy
