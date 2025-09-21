// Copyright 2020 ETH Zurich
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

// @ dup pkgInvariant acc(postInitInvariant(), _)
package epic

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/subtle"
	"encoding/binary"
	"math"
	"time"

	"github.com/scionproto/scion/pkg/addr"
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
)

const (
	// AuthLen denotes the size of the authenticator in bytes
	AuthLen = 16
	// MaxPacketLifetime denotes the maximal lifetime of a packet
	MaxPacketLifetime time.Duration = 2 * time.Second
	// MaxClockSkew denotes the maximal clock skew
	MaxClockSkew time.Duration = time.Second
	// TimestampResolution denotes the resolution of the epic timestamp
	TimestampResolution = 21 * time.Microsecond
	// MACBufferSize denotes the buffer size of the CBC input and output.
	MACBufferSize = 48
)

var zeroInitVector /*@@@*/ [16]byte

// ghost init
// @ func init() {
// @ 	fold acc(sl.Bytes(zeroInitVector[:], 0, len(zeroInitVector[:])), _)
// @ 	fold acc(postInitInvariant(), _)
// @ }

// CreateTimestamp returns the epic timestamp, which encodes the current time (now) relative to the
// input timestamp. The input timestamp must not be in the future (compared to the current time),
// otherwise an error is returned. An error is also returned if the current time is more than 1 day
// and 63 minutes after the input timestamp.
// @ requires input.IsLow() && now.IsLow()
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func CreateTimestamp(input time.Time, now time.Time) (res uint32, err error) {
	if input.After(now) {
		return 0, serrors.New("provided input timestamp is in the future",
			"input", input, "now", now)
	}
	epicTS := now.Sub(input)/TimestampResolution - 1
	if epicTS < 0 {
		epicTS = 0
	}
	if epicTS >= (1 << 32) {
		return 0, serrors.New("diff between input and now >1d63min", "epicTS", epicTS)
	}
	return uint32(epicTS), nil
}

// VerifyTimestamp checks whether an EPIC packet is fresh. This means that the time the packet
// was sent from the source host, which is encoded by the timestamp and the epicTimestamp,
// does not date back more than the maximal packet lifetime of two seconds. The function also takes
// a possible clock drift between the packet source and the verifier of up to one second into
// account.
// @ requires timestamp.IsLow() && low(epicTS) && now.IsLow()
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func VerifyTimestamp(timestamp time.Time, epicTS uint32, now time.Time) (err error) {
	diff := (time.Duration(epicTS) + 1) * TimestampResolution
	tsSender := timestamp.Add(diff)

	if tsSender.After(now.Add(MaxClockSkew)) {
		delta := tsSender.Sub(now.Add(MaxClockSkew))
		return serrors.New("epic timestamp is in the future",
			"delta", delta)
	}
	if now.After(tsSender.Add(MaxPacketLifetime).Add(MaxClockSkew)) {
		delta := now.Sub(tsSender.Add(MaxPacketLifetime).Add(MaxClockSkew))
		return serrors.New("epic timestamp expired",
			"delta", delta)
	}
	return nil
}

// CalcMac derives the EPIC MAC (PHVF/LHVF) given the full 16 bytes of the SCION path type
// MAC (auth), the EPIC packet ID (pktID), the timestamp in the Info Field (timestamp),
// and the SCION common/address header (s).
// If the same buffer is provided in subsequent calls to this function, the previously returned
// EPIC MAC may get overwritten. Only the most recently returned EPIC MAC is guaranteed to be
// valid.
// TODO: re-order since splitting up preserves made it messy
// @ requires  len(auth) == 16
// @ requires  sl.Bytes(buffer, 0, len(buffer))
// @ requires  acc(s.Mem(ub), R20)
// @ requires  acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ requires  low(len(buffer)) && low(s == nil)
// @ requires  acc(sl.Bytes(auth, 0, len(auth)), R30)
// @ requires  low(len(auth)) &&
// @ 	forall i int :: { sl.GetByte(auth, 0, len(auth), i) } 0 <= i && i < len(auth) &&
// @ 		low(i) ==> low(sl.GetByte(auth, 0, len(auth), i))
// @ requires  low(s.GetSrcAddrType(ub)) && low(s.GetSrcIA(ub)) && low(s.GetPayloadLen(ub))
// @ requires  low(s.GetDstAddrType(ub))
// @ requires  low(len(ub)) && 
// @ 	forall i int :: { sl.GetByte(ub, 0, len(ub), i) } slayers.CmnHdrLen <= i && i < len(ub) &&
// @ 		low(i) ==> low(sl.GetByte(ub, 0, len(ub), i))
// @ requires  low(timestamp) && low(pktID)
// @ ensures   acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ ensures   acc(sl.Bytes(auth, 0, len(auth)), R30)
// @ ensures   acc(s.Mem(ub), R20)
// @ ensures   reserr == nil ==> sl.Bytes(res, 0, len(res))
// @ ensures   reserr == nil ==> (sl.Bytes(res, 0, len(res)) --* sl.Bytes(buffer, 0, len(buffer)))
// @ ensures   reserr == nil ==> low(len(res)) &&
// @ 	forall i int :: { sl.GetByte(res, 0, len(res), i) } 0 <= i && i < len(res) &&
// @ 		low(i) ==> low(sl.GetByte(res, 0, len(res), i))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr != nil ==> sl.Bytes(buffer, 0, len(buffer))
// @ ensures   low(reserr != nil)
// @ decreases
func CalcMac(auth []byte, pktID epic.PktID, s *slayers.SCION,
	timestamp uint32, buffer []byte /*@ , ghost ub []byte @*/) (res []byte, reserr error) {

	// @ ghost oldBuffer := buffer
	// @ ghost allocatesNewBuffer := len(buffer) < MACBufferSize
	if len(buffer) < MACBufferSize {
		buffer = make([]byte, MACBufferSize)
		// @ fold sl.Bytes(buffer, 0, len(buffer))
	}

	// Initialize cryptographic MAC function
	f, err := initEpicMac(auth)
	if err != nil {
		return nil, err
	}
	// Prepare the input for the MAC function
	inputLength, err := prepareMacInput(pktID, s, timestamp, buffer /*@, ub @*/)
	if err != nil {
		return nil, err
	}
	// @ assert 16 <= inputLength
	// @ assert f.BlockSize() == 16
	// Calculate Epic MAC = first 4 bytes of the last CBC block
	// @ assert forall i int :: { sl.GetByte(buffer, 0, len(buffer), i) } 0 <= i && i < inputLength &&
	// @ 	low(i) ==> low(sl.GetByte(buffer, 0, len(buffer), i))
	// @ sl.SplitRange_Bytes(buffer, 0, inputLength, writePerm)
	input := buffer[:inputLength]
	// @ assert low(len(input)) && 
	// @ 	forall i int :: { sl.GetByte(input, 0, len(input), i) } 0 <= i && i < len(input) &&
	// @ 		low(i) ==> low(sl.GetByte(input, 0, len(input), i))
	f.CryptBlocks(input, input)
	// @ assert low(len(input)) && 
	// @ 	forall i int :: { sl.GetByte(input, 0, len(input), i) } 0 <= i && i < len(input) &&
	// @ 		low(i) ==> low(sl.GetByte(input, 0, len(input), i))
	// @ ghost start := len(input)-f.BlockSize()
	// @ ghost end   := start + 4
	result := input[len(input)-f.BlockSize() : len(input)-f.BlockSize()+4]
	// @ sl.SplitRange_Bytes(input, start, end, writePerm)
	// TODO: Once Gobra issue #946 is resolved, uncomment.
	//  package (sl.Bytes(result, 0, len(result)) --* sl.Bytes(oldBuffer, 0, len(oldBuffer))) {
	//  	ghost if !allocatesNewBuffer {
	//  		assert oldBuffer === buffer
	//  		sl.CombineRange_Bytes(input, start, end, writePerm)
	//  		sl.CombineRange_Bytes(oldBuffer, 0, inputLength, writePerm)
	//  	}
	//  }
	//  assert (sl.Bytes(result, 0, len(result)) --* sl.Bytes(oldBuffer, 0, len(oldBuffer)))
	// TODO: I don't know if this is quite correct. Do I need to exhale some 
	// permissions (and inhale magic wand) instead?
	// @ assume (sl.Bytes(result, 0, len(result)) --* sl.Bytes(oldBuffer, 0, len(oldBuffer)))
	// NOTE: My assumption does not introduce a (immediate) contradiction, as this fails
	//  assert false
	return result, nil
}

// VerifyHVF verifies the correctness of the HVF (PHVF or the LHVF) field in the EPIC packet by
// recalculating and comparing it. If the EPIC authenticator (auth), which denotes the full 16
// bytes of the SCION path type MAC, has invalid length, or if the MAC calculation gives an error,
// also VerifyHVF returns an error. The verification was successful if and only if VerifyHVF
// returns nil.
// @ requires  acc(sl.Bytes(hvf, 0, len(hvf)), R50)
// @ requires  acc(sl.Bytes(auth, 0, len(auth)), R30)
// @ requires  acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ requires  acc(s.Mem(ub), R20)
// @ requires  low(s == nil) && low(len(auth)) && low(len(buffer))
// @ requires  low(len(hvf)) &&
// @ 	forall i int :: { sl.GetByte(hvf, 0, len(hvf), i) } 0 <= i && i < len(hvf) &&
// @ 		low(i) ==> low(sl.GetByte(hvf, 0, len(hvf), i))
// @ requires  low(len(auth)) &&
// @ 	forall i int :: { sl.GetByte(auth, 0, len(auth), i) } 0 <= i && i < len(auth) &&
// @ 		low(i) ==> low(sl.GetByte(auth, 0, len(auth), i))
// @ requires  low(s.GetSrcAddrType(ub)) && low(s.GetSrcIA(ub)) && low(s.GetPayloadLen(ub))
// @ requires  low(s.GetDstAddrType(ub))
// @ requires  low(len(ub)) && 
// @ 	forall i int :: { sl.GetByte(ub, 0, len(ub), i) } slayers.CmnHdrLen <= i && i < len(ub) &&
// @ 		low(i) ==> low(sl.GetByte(ub, 0, len(ub), i))
// @ requires  low(timestamp) && low(pktID)
// @ preserves sl.Bytes(buffer, 0, len(buffer))
// @ ensures   acc(s.Mem(ub), R20)
// @ ensures   acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ ensures   acc(sl.Bytes(auth, 0, len(auth)), R30)
// @ ensures   acc(sl.Bytes(hvf, 0, len(hvf)), R50)
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func VerifyHVF(auth []byte, pktID epic.PktID, s *slayers.SCION,
	timestamp uint32, hvf []byte, buffer []byte /*@ , ghost ub []byte @*/) (reserr error) {

	if s == nil || len(auth) != AuthLen {
		return serrors.New("invalid input")
	}

	mac, err := CalcMac(auth, pktID, s, timestamp, buffer /*@ , ub @*/)
	if err != nil {
		return err
	}

	// TODO[henri]: Unsure whether it makes sense to have hvf and mac low here.
	// Maybe we need to declassify, but we're outside of IO spec here.
	// But EPIC verification works differently anyway ... so might be OK
	if subtle.ConstantTimeCompare(hvf, mac /*@, R51 @*/) == 0 {
		// @ apply sl.Bytes(mac, 0, len(mac)) --* sl.Bytes(buffer, 0, len(buffer))
		return serrors.New("epic hop validation field verification failed",
			"hvf in packet", hvf, "calculated mac", mac, "auth", auth)
	}
	// @ apply sl.Bytes(mac, 0, len(mac)) --* sl.Bytes(buffer, 0, len(buffer))
	return nil
}

// PktCounterFromCore creates a counter for the packet identifier
// based on the core ID and the core counter.
func PktCounterFromCore(coreID uint8, coreCounter uint32) uint32 {
	return (uint32(coreID) << 24) | (coreCounter & 0x00FFFFFF)
}

// CoreFromPktCounter reads the core ID and the core counter
// from a counter belonging to a packet identifier.
func CoreFromPktCounter(counter uint32) (uint8, uint32) {
	coreID := uint8(counter >> 24)
	coreCounter := counter & 0x00FFFFFF
	return coreID, coreCounter
}

// @ requires  len(key) == 16
// @ requires  acc(sl.Bytes(key, 0, len(key)), R50)
// TODO[henri]: Unsure whether this precondition makes sense here. 
// Maybe contract of `aes.NewCipher` is also too restrictive
// @ requires low(len(key)) && 
// @ 	forall i int :: { sl.GetByte(key, 0, len(key), i) } 0 <= i && i < len(key) &&
// @ 		low(i) ==> low(sl.GetByte(key, 0, len(key), i))
// @ ensures   acc(sl.Bytes(key, 0, len(key)), R50)
// @ ensures   reserr == nil ==>
// @ 	res != nil && res.Mem() && res.BlockSize() == 16 && res.IsLow()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   low(reserr != nil)
// @ decreases
func initEpicMac(key []byte) (res cipher.BlockMode, reserr error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, serrors.New("Unable to initialize AES cipher")
	}

	// @ establishPostInitInvariant()
	// @ unfold acc(postInitInvariant(), _)
	// CBC-MAC = CBC-Encryption with zero initialization vector
	mode := cipher.NewCBCEncrypter(block, zeroInitVector[:])
	return mode, nil
}

// @ requires  MACBufferSize <= len(inputBuffer)
// @ requires  acc(s.Mem(ub), R20)
// @ requires  acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ requires  low(s == nil)
// TODO: might want to abstract this using IsLow function
// @ requires  low(s.GetSrcAddrType(ub)) && low(s.GetDstAddrType(ub))
// @ requires  low(s.GetSrcIA(ub)) && low(s.GetPayloadLen(ub))
// NOTE: The following is to establish that the contents of RawSrcAddr are low,
// as this is === part of `ub` (cf. (*SCION).HeaderMem). Maybe we want to be 
// more direct.
// TODO: might want to make this less specific and mark all of ub low
// @ requires  low(len(ub)) && 
// @ 	forall i int :: { sl.GetByte(ub, 0, len(ub), i) } slayers.CmnHdrLen <= i && i < len(ub) &&
// @ 		low(i) ==> low(sl.GetByte(ub, 0, len(ub), i))
//  requires  IsLowBytes(ub, 0, len(ub), slayers.CmnHdrLen, len(ub))
// @ requires  low(timestamp) && low(pktID)
// @ requires  low(len(inputBuffer))
// @ preserves sl.Bytes(inputBuffer, 0, len(inputBuffer))
// @ ensures   acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ ensures   acc(s.Mem(ub), R20)
// @ ensures   reserr == nil ==> 16 <= res && res <= len(inputBuffer)
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   low(reserr != nil)
// TODO: don't know if for calling function `< res` is OK instead of `< len(inputBuffer)` ...
//  ensures   reserr == nil ==> low(len(inputBuffer)) && 
// TODO: comment in again. would need specialized LowBytes to set bounds
// @ ensures   reserr == nil ==> 
// @ 	forall i int :: { sl.GetByte(inputBuffer, 0, len(inputBuffer), i) } 0 <= i && i < res &&
// @ 		low(i) ==> low(sl.GetByte(inputBuffer, 0, len(inputBuffer), i))
//  ensures  reserr == nil ==> IsLowBytes(inputBuffer, 0, len(inputBuffer), 0, res)
// @ ensures   low(res)
// @ decreases
func prepareMacInput(pktID epic.PktID, s *slayers.SCION, timestamp uint32,
	inputBuffer []byte /*@ , ghost ub []byte @*/) (res int, reserr error) {
	// @ share pktID

	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	//   | flags (1B) | timestamp (4B) |    packet ID (8B)     |
	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	//   | srcIA (8B) | srcAddr (4/8/12/16B) | payloadLen (2B) |
	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	//   | zero padding (0-15B)                                |
	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	// The "flags" field only encodes the length of the source address.

	if s == nil {
		return 0, serrors.New("SCION common+address header must not be nil")
	}
	// @ unfold acc(s.Mem(ub), R20/2)
	// @ defer fold acc(s.Mem(ub), R20/2)
	// @ unfold acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R20/2)
	// @ defer fold acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R20/2)
	srcAddr := s.RawSrcAddr
	// @ ghost start := slayers.CmnHdrLen+2*addr.IABytes+s.DstAddrType.Length()
	// @ ghost end := slayers.CmnHdrLen+2*addr.IABytes+s.DstAddrType.Length()+s.SrcAddrType.Length()
	// @ assert srcAddr === ub[start:end]
	l := len(srcAddr)
	
	// Calculate a multiple of 16 such that the input fits in
	nrBlocks := int(math.Ceil((float64(23) + float64(l)) / float64(16)))
	// (VerifiedSCION) The following assumptions cannot be currently proven due to Gobra's incomplete
	// support for floats.
	// @ assume 23 + l <= nrBlocks * 16
	// @ assume nrBlocks * 16 <= 23 + l + 16
	inputLength := 16 * nrBlocks

	// Fill input
	// @ unfold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	offset := 0
	inputBuffer[0] = uint8(s.SrcAddrType & 0x3) // extract length bits
	offset += 1
	//  assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	//  	low(i) ==> low(inputBuffer[i])
	//  assert reveal IsLowByteSlice(inputBuffer, 0, offset)
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	binary.BigEndian.PutUint32(inputBuffer[offset:], timestamp)
	offset += 4
	//  assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	//  	low(i) ==> low(inputBuffer[i])
	//  assert reveal IsLowByteSlice(inputBuffer, 0, offset)
	// @ fold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	// @ sl.SplitRange_Bytes(inputBuffer, offset, len(inputBuffer), writePerm)
	pktID.SerializeTo(inputBuffer[offset:])
	// @ sl.CombineRange_Bytes(inputBuffer, offset, len(inputBuffer), writePerm)
	offset += epic.PktIDLen
	// @ unfold acc(sl.Bytes(inputBuffer, 0, len(inputBuffer)), HalfPerm)
	// NOTE: Maybe extend to < len(inputBuffer)
    // @ assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset ==>
    // @ 	inputBuffer[i] == sl.GetByte(inputBuffer, 0, len(inputBuffer), i)
	// @ unfold acc(sl.Bytes(inputBuffer, 0, len(inputBuffer)), HalfPerm)
	//  assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	//  	low(i) ==> low(inputBuffer[i])
	//  assert reveal IsLowByteSlice(inputBuffer, 0, offset)
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	binary.BigEndian.PutUint64(inputBuffer[offset:], uint64(s.SrcIA))
	offset += addr.IABytes
	//  assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	//  	low(i) ==> low(inputBuffer[i])
	//  assert reveal IsLowByteSlice(inputBuffer, 0, offset)
	// NOTE: BEGIN OUTLINE EXPERIMENT
	//  assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	//  	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	//  sl.SplitRange_Bytes(ub, start, end, R20)
    //  assert forall i int :: { &srcAddr[i] } 0 <= i && i < len(srcAddr) ==>
    //  	&srcAddr[i] == &ub[start:end][i]
	//  unfold acc(sl.Bytes(srcAddr, 0, len(srcAddr)), R21)
    //  assert forall i int :: { &srcAddr[i] } 0 <= i && i < len(srcAddr) ==>
    //  	srcAddr[i] == sl.GetByte(srcAddr, 0, len(srcAddr), i)
	// copy(inputBuffer[offset:], srcAddr /*@ , R21 @*/)
    //  assert forall i int :: { &inputBuffer[i] } offset <= i && i < offset + l ==>
    //  	inputBuffer[i] == inputBuffer[offset:][i - offset]
	//  fold acc(sl.Bytes(srcAddr, 0, len(srcAddr)), R21)
	//  sl.CombineRange_Bytes(ub, start, end, R20)
	// offset += l
	//  assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	//  	low(i) ==> low(inputBuffer[i])
    // @ requires acc(s.Mem(ub), R22)
    // @ requires acc(&s.DstAddrType, R22) && acc(&s.SrcAddrType, R22)
    // @ requires offset == 5 + epic.PktIDLen + addr.IABytes
    // @ requires start == slayers.CmnHdrLen+2*addr.IABytes+s.DstAddrType.Length()
    // @ requires end == slayers.CmnHdrLen+2*addr.IABytes+s.DstAddrType.Length()+s.SrcAddrType.Length()
    // @ requires MACBufferSize <= len(inputBuffer)
    // @ requires acc(sl.Bytes(ub, 0, len(ub)), R20)
    // @ requires low(len(ub)) && 
    // @     forall i int :: { sl.GetByte(ub, 0, len(ub), i) } slayers.CmnHdrLen <= i && i < len(ub) &&
    // @         low(i) ==> low(sl.GetByte(ub, 0, len(ub), i))
    // @ requires unfolding acc(s.Mem(ub), R22) in unfolding acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R22) in srcAddr === ub[start:end]
    // @ requires acc(inputBuffer)
    // @ requires forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
    // @     low(i) ==> low(inputBuffer[i])
    // @ requires l == len(srcAddr)
    // @ requires low(start) && low(end)
    // @ ensures  offset == 5 + epic.PktIDLen + addr.IABytes + l
    // @ ensures  acc(inputBuffer)
    // @ ensures  MACBufferSize <= len(inputBuffer)
    // @ ensures  forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
    // @     low(i) ==> low(inputBuffer[i])
    // @ ensures  acc(s.Mem(ub), R22)
    // @ ensures  acc(&s.DstAddrType, R22) && acc(&s.SrcAddrType, R22)
    // @ ensures  acc(sl.Bytes(ub, 0, len(ub)), R20)
    // @ decreases
    // @ outline(
        // @ unfold acc(s.Mem(ub), R22)
        // @ unfold acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R22)

        // @ assert srcAddr === ub[start:end]
		// @ assert forall i int :: { sl.GetByte(ub, 0, len(ub), i) } start <= i && i < end &&
		// @ 	low(i) ==> low(sl.GetByte(ub, 0, len(ub), i))

        // @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
        // @     &inputBuffer[offset:][i] == &inputBuffer[offset+i]
        // @ sl.SplitRange_Bytes(ub, start, end, R20)
		// @ assert forall i int :: { sl.GetByte(ub[start:end], 0, len(ub[start:end]), i) } 0 <= i && i < len(ub[start:end]) &&
		// @ 	low(i) ==> low(sl.GetByte(ub[start:end], 0, len(ub[start:end]), i))
        // @ assert forall i int :: { &srcAddr[i] } 0 <= i && i < len(srcAddr) ==>
        // @     &srcAddr[i] == &ub[start:end][i]
		// @ assert forall i int :: { sl.GetByte(srcAddr, 0, len(srcAddr), i) } 0 <= i && i < len(srcAddr) &&
		// @ 	low(i) ==> low(sl.GetByte(srcAddr, 0, len(srcAddr), i))
        // @ unfold acc(sl.Bytes(srcAddr, 0, len(srcAddr)), R21)
        // @ assert forall i int :: { &srcAddr[i] } 0 <= i && i < len(srcAddr) ==>
        // @     srcAddr[i] == sl.GetByte(srcAddr, 0, len(srcAddr), i)
		// @ assert forall i int :: { &srcAddr[i] } 0 <= i && i < len(srcAddr) &&
		// @ 	low(i) ==> low(srcAddr[i])
        copy(inputBuffer[offset:], srcAddr /*@, R21 @*/)
		// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(srcAddr) &&
		// @ 	low(i) ==> low(inputBuffer[offset:][i])
        // @ assert forall i int :: { &inputBuffer[i] } offset <= i && i < offset + l ==>
        // @     inputBuffer[i] == inputBuffer[offset:][i - offset]
        // @ fold acc(sl.Bytes(srcAddr, 0, len(srcAddr)), R21)
        // @ sl.CombineRange_Bytes(ub, start, end, R20)
        offset += l
        // @ assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
        // @    low(i) ==> low(inputBuffer[i])
        
        // @ fold acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R22)
        // @ fold acc(s.Mem(ub), R22)
    // @ )
	// NOTE: END OUTLINE EXPERIMENT
	//  assert reveal IsLowByteSlice(inputBuffer, 0, offset)
	// NOTE: it takes ~13 min. to get here
	// NOTE: with outline block, it once took ~11 min. to get here
	//  assert false
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	binary.BigEndian.PutUint16(inputBuffer[offset:], s.PayloadLen)
	offset += 2
	// NOTE: it takes ~16 min. to get here
	//  assert false
	// TODO: try to uncomment again
	// @ assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	// @ 	low(i) ==> low(inputBuffer[i])
	//  assert reveal IsLowByteSlice(inputBuffer, 0, offset)
	// NOTE: takes at least 40 min., crashed once
	// NOTE: with outline block, it once took ~6 mins.
	//  assert false
	// @ assert offset == 23 + l
	// @ assert offset <= inputLength
	// @ assert inputLength <= len(inputBuffer)
	// @ assert forall i int :: { &inputBuffer[offset:inputLength][i] } 0 <= i && i < len(inputBuffer[offset:inputLength]) ==>
	// @ 	&inputBuffer[offset:inputLength][i] == &inputBuffer[offset+i]
	// @ assert forall i int :: { &inputBuffer[offset:inputLength][i] } 0 <= i && i < len(inputBuffer[offset:inputLength]) ==>
	// @ 	acc(&inputBuffer[offset:inputLength][i])
	// @ establishPostInitInvariant()
	// @ unfold acc(postInitInvariant(), _)
	// @ assert acc(sl.Bytes(zeroInitVector[:], 0, 16), _)
	// (VerifiedSCION) From the pkg invariant, we learn that we have a wildcard access to zeroInitVector.
	// Unfortunately, it is not possible to call `copy` with a wildcard amount, even though
	// that would be perfectly fine. The spec of `copy` would need to be adapted to allow for that case.
	// @ inhale acc(sl.Bytes(zeroInitVector[:], 0, len(zeroInitVector[:])), R55)
	// @ unfold acc(sl.Bytes(zeroInitVector[:], 0, len(zeroInitVector[:])), R55)
	// @ assert forall i int :: { &zeroInitVector[:][i] }{ sl.GetByte(zeroInitVector[:], 0, 16, i) } 0 <= i && i < 16 ==>
	// @ 	zeroInitVector[:][i] == sl.GetByte(zeroInitVector[:], 0, 16, i)
	// @ assert forall i int :: { &zeroInitVector[:][i] } 0 <= i && i < len(zeroInitVector[:]) ==>
	// @ 	&zeroInitVector[:][i] == &zeroInitVector[i]
	// @ assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	// @ 	low(i) ==> low(inputBuffer[i])
	// @ assert forall i int :: { &zeroInitVector[:][i] } 0 <= i && i < len(zeroInitVector[:]) &&
	// @ 	low(i) ==> low(zeroInitVector[:][i])
	copy(inputBuffer[offset:inputLength], zeroInitVector[:] /*@ , R55 @*/)
	// @ assert forall i int :: { &inputBuffer[offset:inputLength][i] } 0 <= i && i < len(inputBuffer[offset:inputLength]) &&
	// @ 	low(i) ==> low(inputBuffer[offset:inputLength][i])
	// @ assert forall i int :: { &inputBuffer[i] } offset <= i && i < inputLength ==>
	// @ 	inputBuffer[i] == inputBuffer[offset:inputLength][i - offset]
	// @ assert forall i int :: { &inputBuffer[i] } offset <= i && i < inputLength &&
	// @ 	low(i) ==> low(inputBuffer[i])
	// @ assert forall i int :: { &inputBuffer[i] } 0 <= i && i < offset &&
	// @ 	low(i) ==> low(inputBuffer[i])
	// @ assert forall i int :: { &inputBuffer[i] } 0 <= i && i < inputLength &&
	// @ 	low(i) ==> low(inputBuffer[i])
	// @ fold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	// @ assert low(len(inputBuffer)) && 
	// @ 	forall i int :: { sl.GetByte(inputBuffer, 0, len(inputBuffer), i) } 0 <= i && i < inputLength &&
	// @ 		low(i) ==> low(sl.GetByte(inputBuffer, 0, len(inputBuffer), i))
	//  assert reveal IsLowBytes(inputBuffer, 0, len(inputBuffer), 0, inputLength)
	//  assert false
	return inputLength, nil
}
