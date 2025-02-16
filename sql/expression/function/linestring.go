// Copyright 2020-2021 Dolthub, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package function

import (
	"fmt"
	"strings"

	"github.com/dolthub/go-mysql-server/sql/expression"

	"github.com/dolthub/go-mysql-server/sql"
)

// Linestring is a function that returns a point type containing values Y and Y.
type Linestring struct {
	expression.NaryExpression
}

var _ sql.FunctionExpression = (*Linestring)(nil)

// NewLinestring creates a new point expression.
func NewLinestring(args ...sql.Expression) (sql.Expression, error) {
	if len(args) < 2 {
		return nil, sql.ErrInvalidArgumentNumber.New("Linestring", "2 or more", len(args))
	}
	return &Linestring{expression.NaryExpression{ChildExpressions: args}}, nil
}

// FunctionName implements sql.FunctionExpression
func (l *Linestring) FunctionName() string {
	return "linestring"
}

// Description implements sql.FunctionExpression
func (l *Linestring) Description() string {
	return "returns a new linestring."
}

// Type implements the sql.Expression interface.
func (l *Linestring) Type() sql.Type {
	return sql.LinestringType{}
}

func (l *Linestring) String() string {
	var args = make([]string, len(l.ChildExpressions))
	for i, arg := range l.ChildExpressions {
		args[i] = arg.String()
	}
	return fmt.Sprintf("LINESTRING(%s)", strings.Join(args, ","))
}

// WithChildren implements the Expression interface.
func (l *Linestring) WithChildren(children ...sql.Expression) (sql.Expression, error) {
	return NewLinestring(children...)
}

// Eval implements the sql.Expression interface.
func (l *Linestring) Eval(ctx *sql.Context, row sql.Row) (interface{}, error) {
	// Allocate array of points
	var points = make([]sql.Point, len(l.ChildExpressions))

	// Go through each argument
	for i, arg := range l.ChildExpressions {
		// Evaluate argument
		val, err := arg.Eval(ctx, row)
		if err != nil {
			return nil, err
		}
		// Must be of type point, throw error otherwise
		switch v := val.(type) {
		case sql.Point:
			points[i] = v
		case sql.Linestring, sql.Polygon: // TODO: eventually add all spatial types
			return nil, sql.ErrInvalidArgumentDetails.New(l.FunctionName(), v)
		default:
			return nil, sql.ErrIllegalGISValue.New(v)
		}
	}

	return sql.Linestring{Points: points}, nil
}
