// Copyright 2017 ETH Zurich
// Copyright 2019 ETH Zurich, Anapaya Systems
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +gobra

package topology

import (
	"strings"

	"github.com/scionproto/scion/pkg/private/serrors"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
	//@ "github.com/scionproto/scion/verification/utils/sif"
)

// LinkType describes inter-AS links.
type LinkType int

// XXX(scrye): These constants might end up in files or on the network, so they should not
// change. They are defined here s.t. they are not subject to the protobuf generator.

const (
	// Unset is used for unknown link types.
	Unset LinkType = 0
	// Core links connect core ASes.
	Core LinkType = 1
	// Parent links are configured on non-core links pointing towards the core of an ISD.
	Parent LinkType = 2
	// Child links are configured on non-core links pointing away from the core of an ISD.
	Child LinkType = 3
	// Peer links are configured for peering relationships.
	Peer LinkType = 4
)

// @ requires low(l)
// SIF: If I wanted to assert `low(res)`, I would need to annotate `error.Error`
// in `builtin.gobra`.
// @ decreases
func (l LinkType) String() (res string) {
	if l == Unset {
		return "unset"
	}
	s, err := l.MarshalText()
	if err != nil {
		return err.Error()
	}
	//@ unfold sif.LowBytes(s, 0, len(s))
	//@ sif.AssumeLowSliceToLowString(s, 1/1)
	return string(s)
}

// LinkTypeFromString returns the numerical link type associated with a string description. If the
// string is not recognized, an Unset link type is returned. The matching is case-insensitive.
// @ requires low(s)
// @ ensures low(res)
// @ decreases
func LinkTypeFromString(s string) (res LinkType) {
	var l /*@@@*/ LinkType
	tmp := []byte(s)
	// SIF: For now I have to make this assumption, see Gobra issue #831
	// Note that we can already infer low(len(tmp)), as the lengths are related
	// in the Viper encoding, but not the contents.
	//@ assume forall i int :: { &tmp[i] } 0 <= i && i < len(tmp) ==> low(tmp[i])
	//@ fold sif.LowBytes(tmp, 0, len(tmp))
	if err := l.UnmarshalText(tmp); err != nil {
		return Unset
	}
	return l
}

// @ requires low(l)
// @ ensures (l == Core || l == Parent || l == Child || l == Peer) == (err == nil)
// @ ensures err == nil ==> sif.LowBytes(res, 0, len(res))
// @ ensures err != nil ==> err.ErrorMem()
// SIF: To make the postconditions as precise as possible, I have not put this
// assertion behind `err == nil` or `err != nil` (resp.)
// Only for LowBytes(...) I have, as that only makes sense when `res != nil`,
// and I have added `low(res)` for `err != nil` appropriately.
// @ ensures low(len(res)) && low(err)
// @ ensures err != nil ==> low(res)
// @ decreases
func (l LinkType) MarshalText() (res []byte, err error) {
	switch l {
	case Core:
		tmp := []byte("core")
		// SIF: ATM we need this assumption, see Gobra issue #831
		//@ assume forall i int :: { tmp[i] } 0 <= i && i < len(tmp) ==> low(tmp[i])
		//@ fold sif.LowBytes(tmp, 0, len(tmp))
		return tmp, nil
	case Parent:
		tmp := []byte("parent")
		//@ assume forall i int :: { tmp[i] } 0 <= i && i < len(tmp) ==> low(tmp[i])
		//@ fold sif.LowBytes(tmp, 0, len(tmp))
		return tmp, nil
	case Child:
		tmp := []byte("child")
		//@ assume forall i int :: { tmp[i] } 0 <= i && i < len(tmp) ==> low(tmp[i])
		//@ fold sif.LowBytes(tmp, 0, len(tmp))
		return tmp, nil
	case Peer:
		tmp := []byte("peer")
		//@ assume forall i int :: { tmp[i] } 0 <= i && i < len(tmp) ==> low(tmp[i])
		//@ fold sif.LowBytes(tmp, 0, len(tmp))
		return tmp, nil
	default:
		return nil, serrors.New("invalid link type")
	}
}

// @ requires low(len(data))
// @ requires acc(sif.LowBytes(data, 0, len(data)), R15)
// @ preserves acc(l)
// @ ensures acc(sl.Bytes(data, 0, len(data)), R15)
// @ ensures err != nil ==> err.ErrorMem()
// SIF: As *l remains unchanged if err != nil, and we don't know if low(*l) before
// @ ensures err == nil ==> low(*l)
// SIF: We need `low(err)` regardless of `err ?= nil` as we use it in branch conditions.
// @ ensures low(err)
// @ decreases
func (l *LinkType) UnmarshalText(data []byte) (err error) {
	//@ unfold acc(sif.LowBytes(data, 0, len(data)), R15)
	//@ ghost defer fold acc(sl.Bytes(data, 0, len(data)), R15)
	//@ sif.AssumeLowSliceToLowString(data, R15)
	switch strings.ToLower(string(data)) {
	case "core":
		*l = Core
	case "parent":
		*l = Parent
	case "child":
		*l = Child
	case "peer":
		*l = Peer
	default:
		// SIF: See Gobra issue #835 for why this assumption is currently necessary
		//@ ghost errCtx := []interface{}{"linkType", string(data)}
		//@ assume forall i int :: { &errCtx[i] } 0 <= i && i < len(errCtx) ==> acc(&errCtx[i]) && low(errCtx[i])
		return serrors.New("invalid link type", "linkType", string(data))
	}
	return nil
}
