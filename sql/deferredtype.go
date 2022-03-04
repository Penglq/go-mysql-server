//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package sql

import (
	"github.com/dolthub/vitess/go/sqltypes"
	"github.com/dolthub/vitess/go/vt/proto/query"
)

var (
	//DeferredType  = deferredType{}

	// ErrValueNotNil is thrown when a value that was expected to be nil, is not
	//ErrValueNotNil = errors.NewKind("value not nil: %#v")
)

type DeferredType interface {
	Type
	IsDeferred() bool
	Name() string
}

type deferredType struct {
	bindVar string
}

var _ DeferredType = (*deferredType)(nil)

func NewDeferredType(name string) Type {
	return &deferredType{bindVar: name}
}

// Compare implements Type interface. Note that while this returns 0 (equals)
// for ordering purposes, in SQL NULL != NULL.
func (t deferredType) Compare(a interface{}, b interface{}) (int, error) {
	return 0, nil
}

// Convert implements Type interface.
func (t deferredType) Convert(v interface{}) (interface{}, error) {
	if v != nil {
		return nil, ErrValueNotNil.New(v)
	}

	return nil, nil
}

// MustConvert implements the Type interface.
func (t deferredType) MustConvert(v interface{}) interface{} {
	value, err := t.Convert(v)
	if err != nil {
		panic(err)
	}
	return value
}

// Promote implements the Type interface.
func (t deferredType) Promote() Type {
	return t
}

// SQL implements Type interface.
func (t deferredType) SQL(interface{}) (sqltypes.Value, error) {
	return sqltypes.NULL, nil
}

// String implements Type interface.
func (t deferredType) String() string {
	return "DEFERRED"
}

// Type implements Type interface.
func (t deferredType) Type() query.Type {
	return sqltypes.Expression
}

// Zero implements Type interface.
func (t deferredType) Zero() interface{} {
	return nil
}

func (t deferredType) IsDeferred() bool {
	return true
}

func (t deferredType) Name() string {
	return t.bindVar
}
