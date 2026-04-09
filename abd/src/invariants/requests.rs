//! Infrastructure of requests issued by clients
//!
//! In general, the way this happens is:
//! - Clients get access to their entire request_id range
//! - When the request is known, the client can commit to it by persisting the kv-pair
use vstd::atomic::PermissionU64;
use vstd::resource::map::GhostMapAuth;
use vstd::resource::map::GhostPersistentPointsTo;
#[cfg(verus_only)]
use vstd::resource::map::GhostPersistentSubmap;
use vstd::resource::map::GhostPointsTo;
use vstd::resource::Loc;

use crate::proto::RequestInner;

use vstd::prelude::*;

verus! {

/// Proof of a particular request being issued by some client
/// The key is (client_id, request_id)
pub type RequestProof = GhostPersistentPointsTo<(u64, u64), RequestInner>;

pub type RequestMapAuth = GhostMapAuth<(u64, u64), RequestInner>;

pub type RequestCtrToken = GhostPointsTo<u64, (u64, int)>;

/// The Request map holds all the proofs of tagging of requests, allowing the system to ensure
/// uniqueness of per-client tags
///
/// The expected workflow is as follows
///     - call [`RequestMap::login`] to receive a token, which is then used in all calls
///     - [`RequestMap::take_permission`] to extract the permission to update an AtomicU64
///     - [`RequestMap::issue_request_proof`] to create the request proof, returning the permission
#[allow(unused)]
pub struct RequestMap {
    /// Map of (client_id, request_id) to the request
    request_auth: RequestMapAuth,
    /// Per client permission, a map from client_id to max seen request_id and id of the permission
    request_ctr_auth: GhostMapAuth<u64, (u64, int)>,
    /// Map from client_id to permission id for the generator request_id (a AtomicU64)
    request_perm: Map<u64, PermissionU64>,
    /// Only one permission at a time may be missing from the map
    ghost missing_perm: Option<(u64, int)>,
}

pub struct RequestMapIds {
    pub request_auth_id: Loc,
    pub request_ctr_id: Loc,
}

impl RequestMap {
    #[verifier::type_invariant]
    pub closed spec fn inv(self) -> bool {
        &&& self.missing_perm is None ==> { self.request_ctr_auth@.dom() == self.request_perm.dom()
        }
        &&& self.missing_perm is Some ==> {
            let missing_client = self.missing_perm->Some_0.0;
            self.request_ctr_auth@.dom() == self.request_perm.dom().insert(missing_client)
        }
        &&& forall|client_id: u64|
            {
                &&& #[trigger] self.request_ctr_auth@.contains_key(client_id)
                &&& #[trigger] self.request_perm.contains_key(client_id)
            } ==> {
                &&& self.request_ctr_auth@[client_id].0 == self.request_perm[client_id].value()
                &&& self.request_ctr_auth@[client_id].1 == self.request_perm[client_id].id()
            }
        &&& forall|cid_rid: (u64, u64)| #[trigger]
            self.request_auth@.contains_key(cid_rid) ==> {
                &&& self.request_ctr_auth@.contains_key(cid_rid.0)
                &&& cid_rid.1 < self.request_ctr_auth@[cid_rid.0].0
            }
    }

    pub open spec fn ids(self) -> RequestMapIds {
        RequestMapIds {
            request_auth_id: self.request_map_id(),
            request_ctr_id: self.request_ctr_map_id(),
        }
    }

    pub closed spec fn is_full(self) -> bool {
        self.missing_perm is None
    }

    pub closed spec fn missing_perm(self) -> (u64, int)
        recommends
            !self.is_full(),
    {
        self.missing_perm->Some_0
    }

    pub closed spec fn request_map_id(self) -> Loc {
        self.request_auth.id()
    }

    pub closed spec fn request_ctr_map_id(self) -> Loc {
        self.request_ctr_auth.id()
    }

    pub closed spec fn issued(self) -> Map<(u64, u64), RequestInner> {
        self.request_auth.view()
    }

    pub closed spec fn request_ctr_map(self) -> Map<u64, (u64, int)> {
        self.request_ctr_auth@
    }

    pub closed spec fn request_perm(self) -> Map<u64, PermissionU64> {
        self.request_perm
    }

    pub proof fn new() -> (tracked r: RequestMap)
        ensures
            r.is_full(),
            r.issued().is_empty(),
            r.request_ctr_map().is_empty(),
            r.request_perm().is_empty(),
    {
        let tracked (request_auth, _empty) = GhostMapAuth::new(Map::empty());

        let tracked (request_ctr_auth, _empty_perms) = GhostMapAuth::new(Map::empty());

        let tracked mut request_perm = Map::tracked_empty();

        let tracked commitments = RequestMap {
            request_auth,
            request_ctr_auth,
            request_perm,
            missing_perm: None,
        };
        commitments
    }

    pub proof fn login(
        tracked &mut self,
        client_id: u64,
        tracked request_perm: PermissionU64,
    ) -> (tracked r: RequestCtrToken)
        requires
            old(self).is_full(),
            !old(self).request_ctr_map().contains_key(client_id),
            request_perm.value() == 0,
        ensures
            self.is_full(),
            self.ids() == old(self).ids(),
            self.issued() == old(self).issued(),
            self.request_ctr_map() == old(self).request_ctr_map().insert(
                client_id,
                (0, request_perm.id()),
            ),
            self.request_perm() == old(self).request_perm().insert(client_id, request_perm),
            r.id() == self.request_ctr_map_id(),
            r.key() == client_id,
            r.value().0 == 0,
            r.value().1 == request_perm.id(),
    {
        use_type_invariant(&*self);
        Self::perm_ctr_insert(
            &mut self.request_perm,
            &mut self.request_ctr_auth,
            client_id,
            request_perm,
        )
    }

    proof fn perm_ctr_insert(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        tracked ctr_auth: &mut GhostMapAuth<u64, (u64, int)>,
        client_id: u64,
        tracked request_perm: PermissionU64,
    ) -> (tracked r: RequestCtrToken)
        requires
            forall|client_id: u64|
                {
                    &&& #[trigger] old(ctr_auth)@.contains_key(client_id)
                    &&& #[trigger] old(perm_map).contains_key(client_id)
                } ==> {
                    &&& old(ctr_auth)@[client_id].0 == old(perm_map)[client_id].value()
                    &&& old(ctr_auth)@[client_id].1 == old(perm_map)[client_id].id()
                },
            !old(ctr_auth)@.contains_key(client_id),
            request_perm.value() == 0,
        ensures
            ctr_auth.id() == old(ctr_auth).id(),
            forall|client_id: u64|
                {
                    &&& #[trigger] ctr_auth@.contains_key(client_id)
                    &&& #[trigger] perm_map.contains_key(client_id)
                } ==> {
                    &&& ctr_auth@[client_id].0 == perm_map[client_id].value()
                    &&& ctr_auth@[client_id].1 == perm_map[client_id].id()
                },
            r.id() == ctr_auth.id(),
            r.key() == client_id,
            r.value().0 == 0,
            r.value().1 == request_perm.id(),
            *perm_map == old(perm_map).insert(client_id, request_perm),
            ctr_auth@ == old(ctr_auth)@.insert(client_id, (0, request_perm.id())),
    {
        let ghost request_perm_id = request_perm.id();
        perm_map.tracked_insert(client_id, request_perm);
        ctr_auth.insert(client_id, (0, request_perm_id))
    }

    pub proof fn take_permission(
        tracked &mut self,
        tracked client_token: &RequestCtrToken,
    ) -> (tracked r: PermissionU64)
        requires
            old(self).is_full(),
            client_token.id() == old(self).request_ctr_map_id(),
        ensures
            !self.is_full(),
            self.ids() == old(self).ids(),
            self.missing_perm() == (client_token.key(), r.id()),
            self.issued() == old(self).issued(),
            self.request_ctr_map() == old(self).request_ctr_map(),
            self.request_perm() == old(self).request_perm().remove(client_token.key()),
            r == old(self).request_perm()[client_token.key()],
            r.id() == client_token.value().1,
            r.value() == client_token.value().0,
    {
        use_type_invariant(&*self);
        assert(client_token.id() == self.request_ctr_map_id());
        client_token.agree(&self.request_ctr_auth);
        Self::remove_permission(&mut self.request_perm, &mut self.missing_perm, client_token)
    }

    proof fn remove_permission(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        missing_perm: &mut Option<(u64, int)>,
        tracked client_token: &RequestCtrToken,
    ) -> (tracked r: PermissionU64)
        requires
            *old(missing_perm) is None,
            old(perm_map).contains_key(client_token.key()),
            old(perm_map)[client_token.key()].id() == client_token.value().1,
            old(perm_map)[client_token.key()].value() == client_token.value().0,
        ensures
            *missing_perm == Some((client_token.key(), old(perm_map)[client_token.key()].id())),
            *perm_map == old(perm_map).remove(client_token.key()),
            r == old(perm_map)[client_token.key()],
            r.id() == client_token.value().1,
            r.value() == client_token.value().0,
    {
        let tracked r = perm_map.tracked_remove(client_token.key());
        *missing_perm = Some((client_token.key(), r.id()));
        r
    }

    pub proof fn issue_request_proof(
        tracked &mut self,
        tracked client_token: &mut RequestCtrToken,
        request_id: u64,
        request: RequestInner,
        tracked client_perm: PermissionU64,
    ) -> (tracked r: RequestProof)
        requires
            !old(self).is_full(),
            old(client_token).id() == old(self).request_ctr_map_id(),
            old(self).missing_perm() == (old(client_token).key(), client_perm.id()),
            request_id == old(client_token).value().0,
            request_id < client_perm.value(),
            client_perm.id() == old(client_token).value().1,
        ensures
            self.is_full(),
            self.ids() == old(self).ids(),
            !old(self).issued().contains_key((client_token.key(), request_id)),
            self.issued() == old(self).issued().insert((client_token.key(), request_id), request),
            self.request_ctr_map() == old(self).request_ctr_map().insert(
                client_token.key(),
                (client_perm.value(), client_perm.id()),
            ),
            self.request_perm() == old(self).request_perm().insert(client_token.key(), client_perm),
            client_token.id() == old(client_token).id(),
            client_token.key() == old(client_token).key(),
            client_token.value().0 == client_perm.value(),
            client_token.value().1 == client_perm.id(),
            r.key() == (client_token.key(), request_id),
            r.value() == request,
            r.value().spec_eq(request),
            r.id() == self.request_map_id(),
    {
        use_type_invariant(&*self);
        let tracked proof = Self::alloc(
            &mut self.request_perm,
            &mut self.request_ctr_auth,
            &mut self.missing_perm,
            &mut self.request_auth,
            client_token,
            request_id,
            request,
            client_perm,
        );
        RequestInner::spec_eq_refl(proof.value());
        proof
    }

    proof fn alloc(
        tracked perm_map: &mut Map<u64, PermissionU64>,
        tracked ctr_auth: &mut GhostMapAuth<u64, (u64, int)>,
        missing_perm: &mut Option<(u64, int)>,
        tracked request_auth: &mut RequestMapAuth,
        tracked client_token: &mut RequestCtrToken,
        request_id: u64,
        request: RequestInner,
        tracked request_perm: PermissionU64,
    ) -> (tracked r: RequestProof)
        requires
            *old(missing_perm) == Some((old(client_token).key(), request_perm.id())),
            old(client_token).id() == old(ctr_auth).id(),
            old(ctr_auth)@.dom() == old(perm_map).dom().insert(old(missing_perm)->Some_0.0),
            request_id == old(client_token).value().0,
            request_id < request_perm.value(),
            request_perm.id() == old(client_token).value().1,
            forall|client_id: u64|
                {
                    &&& #[trigger] old(ctr_auth)@.contains_key(client_id)
                    &&& #[trigger] old(perm_map).contains_key(client_id)
                } ==> {
                    &&& old(ctr_auth)@[client_id].0 == old(perm_map)[client_id].value()
                    &&& old(ctr_auth)@[client_id].1 == old(perm_map)[client_id].id()
                },
            forall|cid_rid: (u64, u64)| #[trigger]
                old(request_auth)@.contains_key(cid_rid) ==> {
                    &&& old(ctr_auth)@.contains_key(cid_rid.0)
                    &&& cid_rid.1 < old(ctr_auth)@[cid_rid.0].0
                },
        ensures
            *missing_perm is None,
            ctr_auth.id() == old(ctr_auth).id(),
            request_auth.id() == old(request_auth).id(),
            client_token.id() == old(client_token).id(),
            !old(request_auth)@.contains_key((client_token.key(), request_id)),
            request_auth@ == old(request_auth)@.insert((client_token.key(), request_id), request),
            ctr_auth@ == old(ctr_auth)@.insert(
                client_token.key(),
                (request_perm.value(), request_perm.id()),
            ),
            *perm_map == old(perm_map).insert(client_token.key(), request_perm),
            ctr_auth@.dom() == perm_map.dom(),
            forall|client_id: u64|
                {
                    &&& #[trigger] ctr_auth@.contains_key(client_id)
                    &&& #[trigger] perm_map.contains_key(client_id)
                } ==> {
                    &&& ctr_auth@[client_id].0 == perm_map[client_id].value()
                    &&& ctr_auth@[client_id].1 == perm_map[client_id].id()
                },
            forall|cid_rid: (u64, u64)| #[trigger]
                request_auth@.contains_key(cid_rid) ==> {
                    &&& ctr_auth@.contains_key(cid_rid.0)
                    &&& cid_rid.1 < ctr_auth@[cid_rid.0].0
                },
            client_token.key() == old(client_token).key(),
            client_token.value().0 == request_perm.value(),
            client_token.value().1 == request_perm.id(),
            r.key() == (client_token.key(), request_id),
            r.value() == request,
            r.id() == request_auth.id(),
    {
        client_token.agree(&*ctr_auth);
        client_token.update(ctr_auth, (request_perm.value(), request_perm.id()));

        // XXX: load bearing
        assert(perm_map.dom().insert(missing_perm->Some_0.0) == ctr_auth@.dom());

        perm_map.tracked_insert(client_token.key(), request_perm);
        *missing_perm = None;
        request_auth.insert((client_token.key(), request_id), request).persist()
    }

    pub proof fn agree_proof(tracked &self, tracked proof: &RequestProof)
        requires
            proof.id() == self.request_map_id(),
        ensures
            self.issued().contains_key(proof.key()),
            self.issued()[proof.key()] == proof.value(),
    {
        use_type_invariant(self);
        proof.agree(&self.request_auth);
    }

    pub proof fn agree_client_token(tracked &self, tracked request_ctr_token: &RequestCtrToken)
        requires
            request_ctr_token.id() == self.request_ctr_map_id(),
        ensures
            self.request_ctr_map().contains_key(request_ctr_token.key()),
    {
        use_type_invariant(self);
        request_ctr_token.agree(&self.request_ctr_auth);
    }
}

} // verus!
