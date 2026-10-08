--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]];
  truckCommands = << >>,
  truckBusy = [t \in Trucks |-> FALSE],
  binCalled = [b \in Bins |-> FALSE],
  binBusy = [b \in Bins |-> FALSE],
  grantedPerm = {},

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
\* Trucks currently idle
AvailableTrucks == {t \in Trucks : ~truckBusy[t]}
Full(b) == Trash(b) + MaxUserTrash \div 2 >= trashCapacity[b]


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.
\* Make sure your formalisations hold for every bin/user, not just one specific instance.

\* For each trash bin, the outer door can only be locked if it is closed.
OuterDoorLocked == \A b \in Bins:
        (~outerDoorLocked[b] \/ ~outerDoorOpen[b])
\* For each trash bin, the vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == \A b \in Bins:
        (~ramExtended[b] \/ outerDoorLocked[b])
\* For each trash bin, every time it is full, it is eventually not full anymore.
TrashEmptied == \A b \in Bins: Full(b) ~> ~Full(b)
\* No unauthorized user can open the outer door of any trash bin.
AuthorizedOpenOnly == \A u  \in Users : 
 (pc[u] \in {"UserOpenDoor", "UserAwaitOpenDoor", "UserDepositTrash","UserCloseDoor"})\*, "UserAwaitClosedDoor"}) 
   => (u \in grantedPerm)


\* Each user infinitely often has trash and infinitely often has no trash.
UserTrash == \A u \in Users: []<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0)
\* For each user, every time they have trash they can deposit their trash.
UserTrashDeposited == \A u \in Users: userTrash[u] > 0 ~> userTrash[u] = 0
\* For each trash bin, every time a truck is requested for it, a truck has eventually emptied it.
TruckEmpties == \A bin \in Bins: binCalled[bin] ~> Trash(bin) = 0

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

macro waitBin(bin) begin
    await binCommand[bin].command = "finished"
end macro



\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        \* Open/Close trap door
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          \* Trash falls through
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        \* Extend/Retract ram
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      \* Non-deterministically choose a bin
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
        \* prevent multiple users from using same bin same time
        await ~binBusy[sBin];
        binBusy[sBin] := TRUE;
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
        binBusy[selectedBin] :=  FALSE; 
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* Remodel it to react to requests and empty the requested trash bin!
fair process truckProcess \in Trucks
variables
    command = [command |-> "idle", bin |-> 1]
begin
  TruckStart:
    while TRUE do 
      ReadCommand:
          await truckCommands /= <<>>;
          truckCommand[self] := [command |-> "empty", bin |-> Head(truckCommands).bin];
          truckCommands := Tail(truckCommands);
      Execute:
          waitBin(truckCommand[self].bin);
          binCommand[truckCommand[self].bin] := [command |-> "empty", open |-> FALSE];
      WaitBinTruck:
          waitBin(truckCommand[self].bin);
          binCalled[truckCommand[self].bin] := FALSE;
          truckCommand[self] := [command |-> "emptied", bin |-> truckCommand[self].bin];
    end while;
end process;



\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control all trash bins in the system and handle requests by users!
fair process controlProcess = Control
variables
  scan = [user |-> 0, bin |-> 0],
  resp = [user |-> 0, permission |-> FALSE]
    
begin
  ControlStart:
    while TRUE do
  ReadCard:
      read(scans, scan);
  AskServer:
      write(serverRequests, [user |-> scan.user]);
  WaitServer:
      read(serverResponses, resp);
  CheckPerm:
      if ~resp.permission then
  ForbidUser:
        permissions[scan.user] := Append(permissions[scan.user],
            [user |-> scan.user, granted |-> FALSE, bin |-> scan.bin]);
        \* unauthorized, abort
        goto ControlStart;
      end if;
  AllowUser:
      \* do not touch a bin that a truck is still busy with
      await ~binCalled[scan.bin];
      grantedPerm := grantedPerm \union {scan.user};
      waitBin(scan.bin);
      binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> TRUE];
  WaitBin1:
      waitBin(scan.bin);
      permissions[scan.user] := Append(permissions[scan.user],
          [user |-> scan.user, granted |-> TRUE, bin |-> scan.bin]);
  WaitDoorClosed:
      await binSensor[scan.bin].sensor = "outer_door_closed";
      binSensor[scan.bin].sensor := "idle";
  LockDoor:
      waitBin(scan.bin);
      binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> FALSE];
      grantedPerm := grantedPerm\{scan.user};
  Trap:
      waitBin(scan.bin);
      binCommand[scan.bin] := [command |-> "change_trap_door", open |-> TRUE];
  Ram:
      waitBin(scan.bin);
      binCommand[scan.bin] := [command |-> "change_ram", open |-> TRUE];
  UnRam:
      waitBin(scan.bin);
      binCommand[scan.bin] := [command |-> "change_ram", open |-> FALSE];
  UnTrap:
      waitBin(scan.bin);
      binCommand[scan.bin] := [command |-> "change_trap_door", open |-> FALSE];
  Empty:
      waitBin(scan.bin);
      if Full(scan.bin) then
        \* call a truck for this bin; control continues serving other bins
        write(truckCommands, [command |-> "empty", bin |-> scan.bin]);
        binCalled[scan.bin] := TRUE;
      end if;
    end while;

end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "af548a84" /\ chksum(tla) = "29b55385")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, truckCommands, 
          truckBusy, binCalled, binBusy, grantedPerm, pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]

AvailableTrucks == {t \in Trucks : ~truckBusy[t]}
Full(b) == Trash(b) + MaxUserTrash \div 2 >= trashCapacity[b]






TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)









OuterDoorLocked == \A b \in Bins:
        (~outerDoorLocked[b] \/ ~outerDoorOpen[b])

RamOuterDoor == \A b \in Bins:
        (~ramExtended[b] \/ outerDoorLocked[b])

TrashEmptied == \A b \in Bins: Full(b) ~> ~Full(b)

AuthorizedOpenOnly == \A u  \in Users :
 (pc[u] \in {"UserOpenDoor", "UserAwaitOpenDoor", "UserDepositTrash","UserCloseDoor"})
   => (u \in grantedPerm)



UserTrash == \A u \in Users: []<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0)

UserTrashDeposited == \A u \in Users: userTrash[u] > 0 ~> userTrash[u] = 0

TruckEmpties == \A bin \in Bins: binCalled[bin] ~> Trash(bin) = 0

VARIABLES perm, selectedBin, req, command, scan, resp

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, 
           truckCommands, truckBusy, binCalled, binBusy, grantedPerm, pc, 
           perm, selectedBin, req, command, scan, resp >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        /\ truckCommands = << >>
        /\ truckBusy = [t \in Trucks |-> FALSE]
        /\ binCalled = [b \in Bins |-> FALSE]
        /\ binBusy = [b \in Bins |-> FALSE]
        /\ grantedPerm = {}
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process truckProcess *)
        /\ command = [self \in Trucks |-> [command |-> "idle", bin |-> 1]]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 0]
        /\ resp = [user |-> 0, permission |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckStart"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 187, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 194, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 197, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 209, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 221, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 222, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 223, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 224, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 225, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 229, column 9.")
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
                                           truckBusy, binCalled, binBusy, 
                                           grantedPerm, perm, selectedBin, req, 
                                           command, scan, resp >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, truckCommands, 
                                            truckBusy, binCalled, binBusy, 
                                            grantedPerm, perm, selectedBin, 
                                            req, command, scan, resp >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
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
                                           truckCommands, truckBusy, binCalled, 
                                           binBusy, grantedPerm, perm, 
                                           selectedBin, req, command, scan, 
                                           resp >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                           /\ ~binBusy[sBin]
                           /\ binBusy' = [binBusy EXCEPT ![sBin] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, truckCommands, truckBusy, 
                                      binCalled, grantedPerm, perm, req, 
                                      command, scan, resp >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 264, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 265, column 7.")
                               /\ IF perm'[self].granted
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
                                               truckBusy, binCalled, binBusy, 
                                               grantedPerm, selectedBin, req, 
                                               command, scan, resp >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, truckCommands, truckBusy, 
                                      binCalled, binBusy, grantedPerm, perm, 
                                      selectedBin, req, command, scan, resp >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           truckCommands, truckBusy, binCalled, 
                                           binBusy, grantedPerm, perm, 
                                           selectedBin, req, command, scan, 
                                           resp >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 272, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, 
                                          truckCommands, truckBusy, binCalled, 
                                          binBusy, grantedPerm, perm, 
                                          selectedBin, req, command, scan, 
                                          resp >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, truckCommands, truckBusy, 
                                       binCalled, binBusy, grantedPerm, perm, 
                                       selectedBin, req, command, scan, resp >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ binBusy' = [binBusy EXCEPT ![selectedBin[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             truckCommands, truckBusy, 
                                             binCalled, grantedPerm, perm, 
                                             selectedBin, req, command, scan, 
                                             resp >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, truckCommands, truckBusy, 
                                      binCalled, binBusy, grantedPerm, perm, 
                                      selectedBin, req, command, scan, resp >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, 
                                       truckCommands, truckBusy, binCalled, 
                                       binBusy, grantedPerm, perm, selectedBin, 
                                       req, command, scan, resp >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, truckCommands, 
                                      truckBusy, binCalled, binBusy, 
                                      grantedPerm, perm, selectedBin, command, 
                                      scan, resp >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckStart(self) == /\ pc[self] = "TruckStart"
                    /\ pc' = [pc EXCEPT ![self] = "ReadCommand"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, truckCommands, truckBusy, 
                                    binCalled, binBusy, grantedPerm, perm, 
                                    selectedBin, req, command, scan, resp >>

ReadCommand(self) == /\ pc[self] = "ReadCommand"
                     /\ truckCommands /= <<>>
                     /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "empty", bin |-> Head(truckCommands).bin]]
                     /\ truckCommands' = Tail(truckCommands)
                     /\ pc' = [pc EXCEPT ![self] = "Execute"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckBusy, binCalled, binBusy, 
                                     grantedPerm, perm, selectedBin, req, 
                                     command, scan, resp >>

Execute(self) == /\ pc[self] = "Execute"
                 /\ binCommand[(truckCommand[self].bin)].command = "finished"
                 /\ binCommand' = [binCommand EXCEPT ![truckCommand[self].bin] = [command |-> "empty", open |-> FALSE]]
                 /\ pc' = [pc EXCEPT ![self] = "WaitBinTruck"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, truckCommands, truckBusy, 
                                 binCalled, binBusy, grantedPerm, perm, 
                                 selectedBin, req, command, scan, resp >>

WaitBinTruck(self) == /\ pc[self] = "WaitBinTruck"
                      /\ binCommand[(truckCommand[self].bin)].command = "finished"
                      /\ binCalled' = [binCalled EXCEPT ![truckCommand[self].bin] = FALSE]
                      /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "emptied", bin |-> truckCommand[self].bin]]
                      /\ pc' = [pc EXCEPT ![self] = "TruckStart"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommands, 
                                      truckBusy, binBusy, grantedPerm, perm, 
                                      selectedBin, req, command, scan, resp >>

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
                                truckBusy, binCalled, binBusy, grantedPerm, 
                                perm, selectedBin, req, command, scan, resp >>

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
                            truckCommands, truckBusy, binCalled, binBusy, 
                            grantedPerm, perm, selectedBin, req, command, resp >>

AskServer == /\ pc[Control] = "AskServer"
             /\ serverRequests' = Append(serverRequests, ([user |-> scan.user]))
             /\ pc' = [pc EXCEPT ![Control] = "WaitServer"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, scans, 
                             permissions, serverResponses, truckCommand, 
                             truckCommands, truckBusy, binCalled, binBusy, 
                             grantedPerm, perm, selectedBin, req, command, 
                             scan, resp >>

WaitServer == /\ pc[Control] = "WaitServer"
              /\ serverResponses /= <<>>
              /\ resp' = Head(serverResponses)
              /\ serverResponses' = Tail(serverResponses)
              /\ pc' = [pc EXCEPT ![Control] = "CheckPerm"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userTrash, binCommand, binSensor, scans, 
                              permissions, serverRequests, truckCommand, 
                              truckCommands, truckBusy, binCalled, binBusy, 
                              grantedPerm, perm, selectedBin, req, command, 
                              scan >>

CheckPerm == /\ pc[Control] = "CheckPerm"
             /\ IF ~resp.permission
                   THEN /\ pc' = [pc EXCEPT ![Control] = "ForbidUser"]
                   ELSE /\ pc' = [pc EXCEPT ![Control] = "AllowUser"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binCommand, binSensor, scans, 
                             permissions, serverRequests, serverResponses, 
                             truckCommand, truckCommands, truckBusy, binCalled, 
                             binBusy, grantedPerm, perm, selectedBin, req, 
                             command, scan, resp >>

ForbidUser == /\ pc[Control] = "ForbidUser"
              /\ permissions' = [permissions EXCEPT ![scan.user] =                       Append(permissions[scan.user],
                                                                   [user |-> scan.user, granted |-> FALSE, bin |-> scan.bin])]
              /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
              /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                              ramExtended, trashInTop, trashCompressed, 
                              trashUncompressed, trashCapacity, trapDestroyed, 
                              userTrash, binCommand, binSensor, scans, 
                              serverRequests, serverResponses, truckCommand, 
                              truckCommands, truckBusy, binCalled, binBusy, 
                              grantedPerm, perm, selectedBin, req, command, 
                              scan, resp >>

AllowUser == /\ pc[Control] = "AllowUser"
             /\ ~binCalled[scan.bin]
             /\ grantedPerm' = (grantedPerm \union {scan.user})
             /\ binCommand[(scan.bin)].command = "finished"
             /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
             /\ pc' = [pc EXCEPT ![Control] = "WaitBin1"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binSensor, scans, permissions, 
                             serverRequests, serverResponses, truckCommand, 
                             truckCommands, truckBusy, binCalled, binBusy, 
                             perm, selectedBin, req, command, scan, resp >>

WaitBin1 == /\ pc[Control] = "WaitBin1"
            /\ binCommand[(scan.bin)].command = "finished"
            /\ permissions' = [permissions EXCEPT ![scan.user] =                       Append(permissions[scan.user],
                                                                 [user |-> scan.user, granted |-> TRUE, bin |-> scan.bin])]
            /\ pc' = [pc EXCEPT ![Control] = "WaitDoorClosed"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userTrash, binCommand, binSensor, scans, 
                            serverRequests, serverResponses, truckCommand, 
                            truckCommands, truckBusy, binCalled, binBusy, 
                            grantedPerm, perm, selectedBin, req, command, scan, 
                            resp >>

WaitDoorClosed == /\ pc[Control] = "WaitDoorClosed"
                  /\ binSensor[scan.bin].sensor = "outer_door_closed"
                  /\ binSensor' = [binSensor EXCEPT ![scan.bin].sensor = "idle"]
                  /\ pc' = [pc EXCEPT ![Control] = "LockDoor"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, scans, 
                                  permissions, serverRequests, serverResponses, 
                                  truckCommand, truckCommands, truckBusy, 
                                  binCalled, binBusy, grantedPerm, perm, 
                                  selectedBin, req, command, scan, resp >>

LockDoor == /\ pc[Control] = "LockDoor"
            /\ binCommand[(scan.bin)].command = "finished"
            /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> FALSE]]
            /\ grantedPerm' = (grantedPerm\{scan.user})
            /\ pc' = [pc EXCEPT ![Control] = "Trap"]
            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                            ramExtended, trashInTop, trashCompressed, 
                            trashUncompressed, trashCapacity, trapDestroyed, 
                            userTrash, binSensor, scans, permissions, 
                            serverRequests, serverResponses, truckCommand, 
                            truckCommands, truckBusy, binCalled, binBusy, perm, 
                            selectedBin, req, command, scan, resp >>

Trap == /\ pc[Control] = "Trap"
        /\ binCommand[(scan.bin)].command = "finished"
        /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_trap_door", open |-> TRUE]]
        /\ pc' = [pc EXCEPT ![Control] = "Ram"]
        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                        ramExtended, trashInTop, trashCompressed, 
                        trashUncompressed, trashCapacity, trapDestroyed, 
                        userTrash, binSensor, scans, permissions, 
                        serverRequests, serverResponses, truckCommand, 
                        truckCommands, truckBusy, binCalled, binBusy, 
                        grantedPerm, perm, selectedBin, req, command, scan, 
                        resp >>

Ram == /\ pc[Control] = "Ram"
       /\ binCommand[(scan.bin)].command = "finished"
       /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_ram", open |-> TRUE]]
       /\ pc' = [pc EXCEPT ![Control] = "UnRam"]
       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                       ramExtended, trashInTop, trashCompressed, 
                       trashUncompressed, trashCapacity, trapDestroyed, 
                       userTrash, binSensor, scans, permissions, 
                       serverRequests, serverResponses, truckCommand, 
                       truckCommands, truckBusy, binCalled, binBusy, 
                       grantedPerm, perm, selectedBin, req, command, scan, 
                       resp >>

UnRam == /\ pc[Control] = "UnRam"
         /\ binCommand[(scan.bin)].command = "finished"
         /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_ram", open |-> FALSE]]
         /\ pc' = [pc EXCEPT ![Control] = "UnTrap"]
         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                         ramExtended, trashInTop, trashCompressed, 
                         trashUncompressed, trashCapacity, trapDestroyed, 
                         userTrash, binSensor, scans, permissions, 
                         serverRequests, serverResponses, truckCommand, 
                         truckCommands, truckBusy, binCalled, binBusy, 
                         grantedPerm, perm, selectedBin, req, command, scan, 
                         resp >>

UnTrap == /\ pc[Control] = "UnTrap"
          /\ binCommand[(scan.bin)].command = "finished"
          /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_trap_door", open |-> FALSE]]
          /\ pc' = [pc EXCEPT ![Control] = "Empty"]
          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                          ramExtended, trashInTop, trashCompressed, 
                          trashUncompressed, trashCapacity, trapDestroyed, 
                          userTrash, binSensor, scans, permissions, 
                          serverRequests, serverResponses, truckCommand, 
                          truckCommands, truckBusy, binCalled, binBusy, 
                          grantedPerm, perm, selectedBin, req, command, scan, 
                          resp >>

Empty == /\ pc[Control] = "Empty"
         /\ binCommand[(scan.bin)].command = "finished"
         /\ IF Full(scan.bin)
               THEN /\ truckCommands' = Append(truckCommands, ([command |-> "empty", bin |-> scan.bin]))
                    /\ binCalled' = [binCalled EXCEPT ![scan.bin] = TRUE]
               ELSE /\ TRUE
                    /\ UNCHANGED << truckCommands, binCalled >>
         /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                         ramExtended, trashInTop, trashCompressed, 
                         trashUncompressed, trashCapacity, trapDestroyed, 
                         userTrash, binCommand, binSensor, scans, permissions, 
                         serverRequests, serverResponses, truckCommand, 
                         truckBusy, binBusy, grantedPerm, perm, selectedBin, 
                         req, command, scan, resp >>

controlProcess == ControlStart \/ ReadCard \/ AskServer \/ WaitServer
                     \/ CheckPerm \/ ForbidUser \/ AllowUser \/ WaitBin1
                     \/ WaitDoorClosed \/ LockDoor \/ Trap \/ Ram \/ UnRam
                     \/ UnTrap \/ Empty

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
\* Last modified Thu Oct 08 14:09:52 CEST 2026 by jerzy
