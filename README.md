# HovercRaft TLA+ Specification

## Overview

This project implements the HovercRaft consensus algorithm using TLA+. The main goal of HovercRaft is to improve the scalability of Raft, particularly the leader's bandwidth bottleneck, by separating the dissemination of large client request payloads from the ordering metadata. This implementation specifically models the "Switch" component as a distinct entity, following specific design requirements.

## HovercRaft vs. Standard Raft: The Core Idea

*   **Standard Raft:** The client sends its request (including the full data payload) to the leader. The leader includes this payload in its log and replicates the log entry (including the payload) to followers. The leader is responsible for both ordering *and* data dissemination.
*   **HovercRaft (as implemented):**
    1.  The client sends its request payload *only* to a distinct **Switch** entity.
    2.  The Switch entity buffers this request.
    3.  The Switch then disseminates the payload to *all Raft Servers* (leader and followers) simultaneously.
    4.  Servers temporarily store these received payloads in their `pendingRequests` buffer.
    5.  The leader is then only responsible for ordering; it selects payloads *it has received from the Switch* and sends small *metadata* messages (referencing the client request payload, e.g., using the payload value itself as an ID) to followers via standard Raft `AppendEntries`.
    6.  Followers match the incoming metadata with the payloads stored in their `pendingRequests` buffer to reconstruct the ordered log.

## Key Changes Implemented

*   **Distinct Switch Entity:** Modeled the "Switch" as a specific constant value (`Switch`) distinct from the Raft `Server` set. Introduced a `Node` set (`Server \union {Switch}`).
*   **Two-Step Payload Dissemination:**
    *   `SwitchClientRequest`: Action for client sending payload *only* to the Switch.
    *   `SwitchDisseminate`: Action for the Switch forwarding a buffered payload to *all* Raft Servers.
*   **Payload/Metadata Separation:** Modified log entries (`LeaderOrderRequest`) and `AppendEntries` messages to handle only metadata (references to payloads) instead of full payloads.
*   **Server Buffering:** Introduced a `pendingRequests` state variable (a function mapping `Node` to a set of payloads) to buffer payloads: on the Switch (from clients) and on Servers (from the Switch).
*   **Matching Logic:** Implemented logic within `HandleAppendEntriesRequest` for followers to match incoming ordering metadata from the leader with their buffered payloads (`pendingRequests[follower_id]`).
*   **Recovery Mechanism:** Added messages (`RecoveryRequest`, `RecoveryResponse`) and logic (`Handle*`) for followers to request missing payloads from the leader if they didn't receive them via the Switch dissemination.

## Detailed Changes by Module

Here's a breakdown of the significant changes made to the original Raft TLA+ files:

### `raftConstants.tla`

*   **Added Constants:** `Switch`, `RecoveryRequest`, `RecoveryResponse`.
*   **Added Definition:** `Node == Server \union {Switch}`.
*   **Why:** Introduced a distinct identifier for the Switch, defined the set of all entities, and added message types for payload recovery.

### `raftVariables.tla`

*   **Added/Modified Variables:**
    *   `pendingRequests`: Declared. Intended structure is `[Node -> SUBSET Value]`. Stores client requests on the Switch, and disseminated requests on Servers.
    *   `missingRequests`: Declared. Intended structure is `[Server -> SUBSET Value]`. Used by followers to track payloads for recovery.
*   **Updated `vars`:** Includes these new variables.

### `raftInit.tla`

*   **Initialization:** Added initialization in `Init` and `MyInit`:
    *   `pendingRequests = [n \in Node |-> {}]`
    *   `missingRequests = [i \in Server |-> {}]`
*   **Why:** Ensures variables start in a known, empty state.

### `raftActionsSolution.tla`

*   **`SwitchClientRequest(v)` (New):** Client sends `v` only to `pendingRequests[Switch]`. Increments `maxc`.
*   **`SwitchDisseminate(v)` (New):** Switch moves `v` from `pendingRequests[Switch]` to `pendingRequests[i]` for all `i \in Server`.
*   **`ClientMulticast(v)` (Replaced):** Replaced by the two actions above.
*   **`LeaderOrderRequest(i, v)` (Modified):** Leader `i` orders `v` from its `pendingRequests[i]`, adds *metadata* to `log[i]`, removes `v` from `pendingRequests[i]`.
*   **`AppendEntries(i, j)` (Modified):** Leader `i` sends *only metadata* from `log[i]` to server `j`.
*   **`HandleAppendEntriesRequest(i, j, m)` (Modified):** Follower `i` checks `pendingRequests[i]` for payload referenced in metadata `m`. If present, appends metadata to log and removes from pending. If missing, replies `FALSE` and triggers recovery (`SendRecoveryRequest`).
*   **`SendRecoveryRequest(i, j, v)` (New):** Creates and sends `RecoveryRequest`.
*   **`HandleRecoveryRequest(i, j, m)` (New):** Leader `i` handles request from `j`, checks log, sends `RecoveryResponse` if found.
*   **`HandleRecoveryResponse(i, j, m)` (New):** Follower `i` handles response from `j`, adds payload to `pendingRequests[i]`, removes from `missingRequests[i]`.
*   **`ClientRequest(i, v)` (Inactive):** Definition kept but excluded from `Next`/`MyNext`.

### `raftSpec.tla`

*   **`Receive(m)` (Modified):** Added routing for `RecoveryRequest`/`Response`. Added `i \in Server`, `j \in Server` checks.
*   **`Next` / `MyNext` (Modified):** Use `SwitchClientRequest`, `SwitchDisseminate`, `LeaderOrderRequest`.
*   **`SpecAddSwitch` / `MyNextAddSwitch` (Added):** Minimal spec for testing `SwitchClientRequest`.

### Configuration (`.cfg` File / Model Overview)

*   **Constants:** Requires defining model values for `Server`, `Switch`, `Value`, message types, bounds (`MaxClientRequests`, etc.).
*   **Specification:** Target `MySpec` (full check) or `SpecAddSwitch` (test).
*   **Invariants:** Select safety invariants (`LogInv`, etc.) for `MySpec` or test invariant for `SpecAddSwitch`.

## How to Run the Model

1.  **Open TLA+ Toolbox.**
2.  **Open Spec:** Open `raftSpec.tla`.
3.  **Create/Open Model.**
4.  **Configure Model:**
    *   **Behavior Spec:** `MySpec` or `SpecAddSwitch`.
    *   **Constants:** Define `Server`, `Switch`, `Value`, bounds, etc. (e.g., `Server <- {"r1", "r2", "r3"}`, `Switch <- "sw"`, `Value <- {"v1", "v2"}`, `MaxClientRequests <- 2`).
    *   **View:** `vars`.
    *   **Constraints:** Add `MyConstraint`.
    *   **Invariants:** Select appropriately (Safety invariants for `MySpec`, `MaxCInvariantForSwitchTest` for `SpecAddSwitch`).
5.  **Run TLC.**
6.  **Analyze:** Check results. No errors on `MySpec` (with safety invariants) indicates success. Violation of `MaxCInvariantForSwitchTest` on `SpecAddSwitch` is expected.
![image](https://github.com/user-attachments/assets/e98ac05e-f675-4ecf-9e12-72a617450fb1)
![image](https://github.com/user-attachments/assets/b2a5b0ad-f105-442a-ac1b-ecbbb4e08e3c)
![Uploading image.png…]()

## Contributor
*   **ovidiu-cristian**
*   **Parsa**
