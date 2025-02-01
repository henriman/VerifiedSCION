// Copyright 2017 ETH Zurich
// Copyright 2020 ETH Zurich, Anapaya Systems
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

package underlay

import (
	"encoding/json"
	"fmt"
	"strings"

	"github.com/scionproto/scion/pkg/private/serrors"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
)

type Type int

const (
	Invalid Type = iota
	UDPIPv4
	UDPIPv6
	UDPIPv46
)

const (
	UDPIPv4Name  = "UDP/IPv4"
	UDPIPv6Name  = "UDP/IPv6"
	UDPIPv46Name = "UDP/IPv4+6"
)

const (
	// EndhostPort is the underlay port that the dispatcher binds to on non-routers. Subject to
	// change during standardisation.
	EndhostPort = 30041
)

// SIF: Branch conditions (mostly) need to be `low`
// @ requires low(o)
// @ ensures low(res)
func (o Type) String() (res string) {
	switch o {
	case UDPIPv4:
		return UDPIPv4Name
	case UDPIPv6:
		return UDPIPv6Name
	case UDPIPv46:
		return UDPIPv46Name
	default:
		return fmt.Sprintf("UNKNOWN (%d)", o)
	}
}

// SIF: Branch conditions (mostly) need to be `low`
// @ requires low(s)
// @ ensures low(t) && low(err)
func TypeFromString(s string) (t Type, err error) {
	switch strings.ToLower(s) {
	case strings.ToLower(UDPIPv4Name):
		return UDPIPv4, nil
	case strings.ToLower(UDPIPv6Name):
		return UDPIPv6, nil
	case strings.ToLower(UDPIPv46Name):
		return UDPIPv46, nil
	default:
		return Invalid, serrors.New("Unknown underlay type", "type", s)
	}
}

// SIF: I am not annotating these methods (for now), as they can't be called
// from the router anyway (cf. verification/utils/definitions/definitions.gobra)
// @ trusted
// @ requires Uncallable()
func (ot *Type) UnmarshalJSON(data []byte) error {
	var strVal string
	if err := json.Unmarshal(data, &strVal); err != nil {
		return err
	}
	t, err := TypeFromString(strVal)
	if err != nil {
		return err
	}
	*ot = t
	return nil
}

// @ trusted
// @ requires Uncallable()
func (ot Type) MarshalJSON() ([]byte, error) {
	return json.Marshal(ot.String())
}

// SIF: Branch conditions (mostly) need to be `low`
// @ requires low(ot)
// @ ensures low(res)
func (ot Type) IsUDP() (res bool) {
	switch ot {
	case UDPIPv4, UDPIPv6, UDPIPv46:
		return true
	}
	return false
}
