from collections import deque


class Closure:
    """Maintain C(x,z) <- E(x,z) or C(x,y) and E(y,z).

    support(x,z) counts the direct edge E(x,z) plus each distinct
    final-edge witness y with C(x,y) and E(y,z); a pair is present
    exactly while its support is positive. Insertions adjust these
    counts and only absent/present transitions propagate downstream.

    Deletion cannot trust the same cascade: inside a cycle the
    remaining witnesses may keep each other's counts positive after
    every real path through the removed edge is gone. Deletion
    therefore retracts exactly the relations whose paths may have used
    the removed edge, then rederives the ones still supported by
    intact edges and relations. Relations outside that region keep all
    their paths, witnesses, and counts, so they are never touched.
    """
    def __init__(self, store):
        self.store = store

    def _adjust(self, src, dst, delta, pending):
        old = self.store.support(src, dst)
        new = old + delta
        if new < 0:
            raise RuntimeError("negative closure support")
        self.store.set_support(src, dst, new)
        if (old == 0) != (new == 0):
            pending.append((src, dst))

    def _drain(self, pending, delta):
        while pending:
            src, middle = pending.popleft()
            for dst in self.store.outgoing(middle):
                self._adjust(src, dst, delta, pending)

    def insert(self, src, dst):
        if self.store.has_edge(src, dst):
            return
        predecessors = self.store.predecessors(src)
        self.store.add_edge(src, dst)
        pending = deque()
        self._adjust(src, dst, 1, pending)
        for root in predecessors:
            self._adjust(root, dst, 1, pending)
        self._drain(pending, 1)

    def delete(self, src, dst):
        store = self.store
        if not store.has_edge(src, dst):
            return
        # A path uses edge (src, dst) iff it starts at src or a root
        # reaching src, and ends at dst or a front reachable from dst.
        # Only relations in roots x fronts can lose support.
        roots = set(store.predecessors(src))
        roots.add(src)
        fronts = set(store.successors(dst))
        fronts.add(dst)
        store.remove_edge(src, dst)
        # Tentatively retract every affected relation.
        dropped = []
        for root in sorted(roots):
            for front in sorted(fronts):
                if store.support(root, front):
                    store.set_support(root, front, 0)
                    dropped.append((root, front))
        # Rederive: a dropped relation survives iff some intact edge
        # y->front still has y == root or an intact C(root, y) behind
        # it. Confirmations then propagate within the dropped region.
        incoming = {}
        tally = {}
        queue = deque()
        for root, front in dropped:
            if front not in incoming:
                incoming[front] = store.incoming(front)
            count = 0
            for y in incoming[front]:
                if y == root or store.support(root, y):
                    count += 1
            tally[(root, front)] = count
            if count:
                queue.append((root, front))
        outgoing = {}
        region = set(tally)
        while queue:
            root, y = queue.popleft()
            if y not in outgoing:
                outgoing[y] = store.outgoing(y)
            for front in outgoing[y]:
                pair = (root, front)
                if pair in region:
                    if tally[pair] == 0:
                        queue.append(pair)
                    tally[pair] += 1
        for (root, front), count in tally.items():
            if count:
                store.set_support(root, front, count)

    def apply(self, add, remove):
        for src, dst in sorted(remove):
            self.delete(src, dst)
        for src, dst in sorted(add):
            self.insert(src, dst)
