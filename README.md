# HovercRaft TLA+ Specification
## Overview
This project implements the HovercRaft consensus algorithm. The main goal of HovercRaft is to improve the scalability of Raft, particularly the leader's bandwidth bottleneck, by separating the dissemination of large client request payloads from the ordering metadata.
## HovercRaft vs. Standard Raft: The Core Idea
*   **Standard Raft:** The client sends its request (including the full data payload) to the leader. The leader includes this payload in its log and replicates the log entry (including the payload) to followers. The leader is responsible for both ordering *and* data dissemination.
*   **HovercRaft:** The client sends its request payload *via a "Switch"* (like IP Multicast or a dedicated proxy) directly to *all* servers (leader and followers) simultaneously. Servers temporarily store these payloads. The leader is then only responsible for ordering; it sends small *metadata* messages (referencing the client request payload) to followers. Followers match the incoming metadata with the stored payloads to reconstruct the ordered log.
## Key Changes Implemented
*   **Switch Simulation:** Modeled the "Switch" mechanism delivering client payloads to all servers.
*   **Payload/Metadata Separation:** Modified log entries and `AppendEntries` messages to handle only metadata (references to payloads) instead of full payloads.
*   **Follower Buffering:** Introduced state variables for followers to store payloads received from the Switch before they are ordered by the leader.
*   **Matching Logic:** Implemented logic for followers to match incoming ordering metadata from the leader with their buffered payloads.
*   **Recovery Mechanism:** Added messages and logic for followers to request missing payloads from the leader if they didn't receive them via the initial multicast.
## Detailed Changes by Module
Here's a breakdown of the significant changes made to the original Raft TLA+ files:
### `raftConstants.tla`
*   **Added Constants:** `RecoveryRequest`, `RecoveryResponse`
*   **Why:** These new constants define the message types needed for the payload recovery mechanism, where a follower asks the leader (or potentially peers) for a payload it missed during the multicast.
### `raftVariables.tla`
*   **Added Variables:**
    *   `pendingRequests`: A mapping from each server ID to a *set* of `Value` (payloads).
    *   `missingRequests`: A mapping from each server ID to a *set* of `Value` (payloads).
*   **Why:**
    *   `pendingRequests` acts as the temporary buffer on each server (leader and followers) to store the payloads received via the `ClientMulticast` (Switch simulation) before they are ordered by the leader's metadata.
    *   `missingRequests` is used by followers to keep track of which payloads they have identified as missing (metadata arrived, but payload not in `pendingRequests`) and have initiated recovery for. This prevents redundant recovery requests.
*   **Updated `vars`:** The tuple `vars` (used for `UNCHANGED` and model view) was updated to include these new variables.
### `raftInit.tla`
*   **Initialization:** Added initialization for `pendingRequests` and `missingRequests` to empty sets (`{}`) for each server in both `Init` and `MyInit`.
*   **Why:** Ensures these new state variables start in a known, empty state at the beginning of the model execution.
### `raftActionsSolution.tla` (Major Changes Here)
*   **`ClientMulticast(v)` Action (New):**
    *   **What:** Takes a payload `v` and adds it to *every* server's `pendingRequests` set. Increments `maxc`.
    *   **Why:** This action simulates the client sending its request payload via the Switch, which reliably (or unreliably, depending on how you model network loss later) delivers it to all servers' buffers simultaneously. This replaces the old `ClientRequest` for the *payload dissemination* part.
*   **`LeaderOrderRequest(i, v)` Action (New):**
    *   **What:** Allows the leader `i` to choose a payload `v` *that is already present in its own `pendingRequests`*. It then creates a *metadata-only* log entry `[term |-> ..., value |-> v]` and appends it to its log. It also removes `v` from its *own* `pendingRequests`.
    *   **Why:** This models the leader's *ordering* responsibility. It only decides the order for payloads it has already received via multicast. It decouples ordering from payload reception and ensures the leader doesn't have to wait for the client directly.
*   **`AppendEntries(i, j)` Action (Modified):**
    *   **What:** Changed to retrieve the *metadata entry* (`[term |-> ..., value |-> v]`) from the leader's log at `nextIndex[i][j]` and send *only this metadata* in the `mentries` field of the `AppendEntriesRequest` message.
    *   **Why:** This is the core of HovercRaft's payload separation. The leader no longer sends bulky payloads in `AppendEntries`, only the small ordering information (term and the value `v` which acts as a reference/ID).
*   **`HandleAppendEntriesRequest(i, j, m)` Action (Modified):**
    *   **What:** This follower logic was significantly changed:
        1.  It still performs standard Raft checks (term, log matching via `logOk`).
        2.  When it receives a non-empty metadata entry (`m.mentries[1]`), it extracts the payload reference (`payloadValue = m.mentries[1].value`).
        3.  **Crucially:** It checks if `payloadValue \in pendingRequests[i]`.
        4.  If **YES** (payload available): It appends the *metadata entry* to its log, removes `payloadValue` from `pendingRequests[i]`, and replies `msuccess = TRUE`.
        5.  If **NO** (payload missing): It replies `msuccess = FALSE`. It then checks if `payloadValue` is already in `missingRequests[i]`. If not, it adds it to `missingRequests'` and triggers sending a `RecoveryRequest` (using the `SendRecoveryRequest` helper action).
    *   **Why:** This implements the follower's responsibility to buffer payloads and match them with the leader's ordering metadata. It also incorporates the trigger for the recovery mechanism when a mismatch (missing payload) occurs.
*   **`SendRecoveryRequest(i, j, v)` Action (New Helper):**
    *   **What:** Creates and sends a `RecoveryRequest` message from follower `i` to leader `j` for payload `v`.
    *   **Why:** Encapsulates the message sending part of the recovery process, called by `HandleAppendEntriesRequest`.
*   **`HandleRecoveryRequest(i, j, m)` Action (New):**
    *   **What:** Handles `RecoveryRequest` messages received by the leader `i`. It checks if its *own log* contains an entry for the requested value. If yes, it sends a `RecoveryResponse` containing the value back to the follower `j`.
    *   **Why:** Allows the leader to serve missing payloads to followers based on its ordered log state.
*   **`HandleRecoveryResponse(i, j, m)` Action (New):**
    *   **What:** Handles `RecoveryResponse` messages received by follower `i`. It adds the received `recoveredValue` to its `pendingRequests` set and removes it from its `missingRequests` set.
    *   **Why:** Completes the recovery loop. The follower now has the payload and can process the corresponding `AppendEntries` metadata when the leader retries sending it.
*   **`ClientRequest(i, v)` Action (Original - Kept but Inactive in `Next`):**
    *   **What:** The original action where the leader directly appends a client value.
    *   **Why:** Kept the definition for reference/completeness, but it **must be excluded** from the `Next` state relation in `raftSpec.tla` when running the HovercRaft model to ensure only the new `ClientMulticast` -> `LeaderOrderRequest` flow is used.
### `raftSpec.tla`
*   **`Receive(m)` Action (Modified):**
    *   **What:** Added disjuncts (`\/ /\`) to handle the new message types `RecoveryRequest` and `RecoveryResponse` by calling their respective handler actions (`HandleRecoveryRequest`, `HandleRecoveryResponse`).
    *   **Why:** Ensures the specification correctly routes incoming recovery messages to the appropriate logic.
*   **`Next` / `MyNext` State Relation (Modified):**
    *   **What:** Replaced the original `ClientRequest` action invocation with `ClientMulticast` and `LeaderOrderRequest`. The call to `Receive(m)` now implicitly covers all message types, including the new ones.
    *   **Why:** Defines the valid state transitions for the HovercRaft model, ensuring the system evolves according to the new message flow (multicast payload -> leader orders -> leader sends metadata -> follower matches/recovers).
### Configuration (`.cfg` File)
*   **Constants:** Added assignments for the new constants (`RecoveryRequest = M_RecoveryRequest`, etc.).
*   **Specification:** Ensured it points to `MySpec` (or `Spec` if using the full `Next`) which uses the HovercRaft actions.
*   **Why:** Provides concrete values for constants needed by the TLC model checker and selects the correct behavior specification to check.
## How to Run the Model
1.  **Open TLA+ Toolbox.**
2.  **Open the Spec:** `File -> Open Spec -> Add New Spec...` and select the main `.tla` file (e.g., `raftSpec.tla`).
3.  **Create a Model:** `TLC Model Checker -> New Model...` (e.g., name it `HovercRaftModel`).
4.  **Configure:**
    *   Behavior Spec: `MySpec` (or `Spec`)
    *   Constants: Load the updated `.cfg` file or define them manually, ensuring `RecoveryRequest` and `RecoveryResponse` are included.
    *   View: `vars`
    *   Constraints: `MyConstraint`
    *   Invariants: Check the desired invariants (e.g., `LogInv`, `MoreThanOneLeaderInv`, etc.).
5.  **Run:** Click the "Run" button.
6.  **Analyze:** Check for invariant violations and examine error traces if any occur.
## Contributor
*   **Parsa**
