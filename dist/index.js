'use strict';

function _interopDefault (ex) { return (ex && (typeof ex === 'object') && 'default' in ex) ? ex['default'] : ex; }

var React = require('react');
var React__default = _interopDefault(React);
var cx = _interopDefault(require('classnames'));
var reactDom = require('react-dom');
var reactRnd = require('react-rnd');
var safeEval = _interopDefault(require('safe-eval'));
var nanoid = _interopDefault(require('nanoid'));

function unwrapExports (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

var reactIs_production_min = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports,"__esModule",{value:!0});
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?Symbol.for("react.memo"):
60115,r=b?Symbol.for("react.lazy"):60116;function t(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case h:return a;default:return u}}case r:case q:case d:return u}}}function v(a){return t(a)===m}exports.typeOf=t;exports.AsyncMode=l;exports.ConcurrentMode=m;exports.ContextConsumer=k;exports.ContextProvider=h;exports.Element=c;exports.ForwardRef=n;
exports.Fragment=e;exports.Lazy=r;exports.Memo=q;exports.Portal=d;exports.Profiler=g;exports.StrictMode=f;exports.Suspense=p;exports.isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||"object"===typeof a&&null!==a&&(a.$$typeof===r||a.$$typeof===q||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n)};exports.isAsyncMode=function(a){return v(a)||t(a)===l};exports.isConcurrentMode=v;exports.isContextConsumer=function(a){return t(a)===k};
exports.isContextProvider=function(a){return t(a)===h};exports.isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};exports.isForwardRef=function(a){return t(a)===n};exports.isFragment=function(a){return t(a)===e};exports.isLazy=function(a){return t(a)===r};exports.isMemo=function(a){return t(a)===q};exports.isPortal=function(a){return t(a)===d};exports.isProfiler=function(a){return t(a)===g};exports.isStrictMode=function(a){return t(a)===f};
exports.isSuspense=function(a){return t(a)===p};
});

unwrapExports(reactIs_production_min);
var reactIs_production_min_1 = reactIs_production_min.typeOf;
var reactIs_production_min_2 = reactIs_production_min.AsyncMode;
var reactIs_production_min_3 = reactIs_production_min.ConcurrentMode;
var reactIs_production_min_4 = reactIs_production_min.ContextConsumer;
var reactIs_production_min_5 = reactIs_production_min.ContextProvider;
var reactIs_production_min_6 = reactIs_production_min.Element;
var reactIs_production_min_7 = reactIs_production_min.ForwardRef;
var reactIs_production_min_8 = reactIs_production_min.Fragment;
var reactIs_production_min_9 = reactIs_production_min.Lazy;
var reactIs_production_min_10 = reactIs_production_min.Memo;
var reactIs_production_min_11 = reactIs_production_min.Portal;
var reactIs_production_min_12 = reactIs_production_min.Profiler;
var reactIs_production_min_13 = reactIs_production_min.StrictMode;
var reactIs_production_min_14 = reactIs_production_min.Suspense;
var reactIs_production_min_15 = reactIs_production_min.isValidElementType;
var reactIs_production_min_16 = reactIs_production_min.isAsyncMode;
var reactIs_production_min_17 = reactIs_production_min.isConcurrentMode;
var reactIs_production_min_18 = reactIs_production_min.isContextConsumer;
var reactIs_production_min_19 = reactIs_production_min.isContextProvider;
var reactIs_production_min_20 = reactIs_production_min.isElement;
var reactIs_production_min_21 = reactIs_production_min.isForwardRef;
var reactIs_production_min_22 = reactIs_production_min.isFragment;
var reactIs_production_min_23 = reactIs_production_min.isLazy;
var reactIs_production_min_24 = reactIs_production_min.isMemo;
var reactIs_production_min_25 = reactIs_production_min.isPortal;
var reactIs_production_min_26 = reactIs_production_min.isProfiler;
var reactIs_production_min_27 = reactIs_production_min.isStrictMode;
var reactIs_production_min_28 = reactIs_production_min.isSuspense;

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

Object.defineProperty(exports, '__esModule', { value: true });

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;

var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace;
var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' ||
  // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE);
}

/**
 * Forked from fbjs/warning:
 * https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/__forks__/warning.js
 *
 * Only change is we use console.warn instead of console.error,
 * and do nothing when 'console' is not supported.
 * This really simplifies the code.
 * ---
 * Similar to invariant but only logs a warning if the condition is not met.
 * This can be used to log issues in development environments in critical
 * paths. Removing the logging code for production environments will keep the
 * same logic and follow the same code paths.
 */

var lowPriorityWarning = function () {};

{
  var printWarning = function (format) {
    for (var _len = arguments.length, args = Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
      args[_key - 1] = arguments[_key];
    }

    var argIndex = 0;
    var message = 'Warning: ' + format.replace(/%s/g, function () {
      return args[argIndex++];
    });
    if (typeof console !== 'undefined') {
      console.warn(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };

  lowPriorityWarning = function (condition, format) {
    if (format === undefined) {
      throw new Error('`lowPriorityWarning(condition, format, ...args)` requires a warning ' + 'message argument');
    }
    if (!condition) {
      for (var _len2 = arguments.length, args = Array(_len2 > 2 ? _len2 - 2 : 0), _key2 = 2; _key2 < _len2; _key2++) {
        args[_key2 - 2] = arguments[_key2];
      }

      printWarning.apply(undefined, [format].concat(args));
    }
  };
}

var lowPriorityWarning$1 = lowPriorityWarning;

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;
    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;
          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;
              default:
                return $$typeof;
            }
        }
      case REACT_LAZY_TYPE:
      case REACT_MEMO_TYPE:
      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
}

// AsyncMode is deprecated along with isAsyncMode
var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;

var hasWarnedAboutDeprecatedIsAsyncMode = false;

// AsyncMode should be deprecated
function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true;
      lowPriorityWarning$1(false, 'The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }
  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.typeOf = typeOf;
exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isValidElementType = isValidElementType;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
  })();
}
});

unwrapExports(reactIs_development);
var reactIs_development_1 = reactIs_development.typeOf;
var reactIs_development_2 = reactIs_development.AsyncMode;
var reactIs_development_3 = reactIs_development.ConcurrentMode;
var reactIs_development_4 = reactIs_development.ContextConsumer;
var reactIs_development_5 = reactIs_development.ContextProvider;
var reactIs_development_6 = reactIs_development.Element;
var reactIs_development_7 = reactIs_development.ForwardRef;
var reactIs_development_8 = reactIs_development.Fragment;
var reactIs_development_9 = reactIs_development.Lazy;
var reactIs_development_10 = reactIs_development.Memo;
var reactIs_development_11 = reactIs_development.Portal;
var reactIs_development_12 = reactIs_development.Profiler;
var reactIs_development_13 = reactIs_development.StrictMode;
var reactIs_development_14 = reactIs_development.Suspense;
var reactIs_development_15 = reactIs_development.isValidElementType;
var reactIs_development_16 = reactIs_development.isAsyncMode;
var reactIs_development_17 = reactIs_development.isConcurrentMode;
var reactIs_development_18 = reactIs_development.isContextConsumer;
var reactIs_development_19 = reactIs_development.isContextProvider;
var reactIs_development_20 = reactIs_development.isElement;
var reactIs_development_21 = reactIs_development.isForwardRef;
var reactIs_development_22 = reactIs_development.isFragment;
var reactIs_development_23 = reactIs_development.isLazy;
var reactIs_development_24 = reactIs_development.isMemo;
var reactIs_development_25 = reactIs_development.isPortal;
var reactIs_development_26 = reactIs_development.isProfiler;
var reactIs_development_27 = reactIs_development.isStrictMode;
var reactIs_development_28 = reactIs_development.isSuspense;

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret;

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning$1(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning$1(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has$1(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning$1(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
          return null;
        }
      }

      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from
      // props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

var AutosizeInput_1 = createCommonjsModule(function (module, exports) {

Object.defineProperty(exports, "__esModule", {
	value: true
});

var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();



var _react2 = _interopRequireDefault(React__default);



var _propTypes2 = _interopRequireDefault(propTypes);

function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

function _objectWithoutProperties(obj, keys) { var target = {}; for (var i in obj) { if (keys.indexOf(i) >= 0) continue; if (!Object.prototype.hasOwnProperty.call(obj, i)) continue; target[i] = obj[i]; } return target; }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

var sizerStyle = {
	position: 'absolute',
	top: 0,
	left: 0,
	visibility: 'hidden',
	height: 0,
	overflow: 'scroll',
	whiteSpace: 'pre'
};

var INPUT_PROPS_BLACKLIST = ['extraWidth', 'injectStyles', 'inputClassName', 'inputRef', 'inputStyle', 'minWidth', 'onAutosize', 'placeholderIsMinWidth'];

var cleanInputProps = function cleanInputProps(inputProps) {
	INPUT_PROPS_BLACKLIST.forEach(function (field) {
		return delete inputProps[field];
	});
	return inputProps;
};

var copyStyles = function copyStyles(styles, node) {
	node.style.fontSize = styles.fontSize;
	node.style.fontFamily = styles.fontFamily;
	node.style.fontWeight = styles.fontWeight;
	node.style.fontStyle = styles.fontStyle;
	node.style.letterSpacing = styles.letterSpacing;
	node.style.textTransform = styles.textTransform;
};

var isIE = typeof window !== 'undefined' && window.navigator ? /MSIE |Trident\/|Edge\//.test(window.navigator.userAgent) : false;

var generateId = function generateId() {
	// we only need an auto-generated ID for stylesheet injection, which is only
	// used for IE. so if the browser is not IE, this should return undefined.
	return isIE ? '_' + Math.random().toString(36).substr(2, 12) : undefined;
};

var AutosizeInput = function (_Component) {
	_inherits(AutosizeInput, _Component);

	function AutosizeInput(props) {
		_classCallCheck(this, AutosizeInput);

		var _this = _possibleConstructorReturn(this, (AutosizeInput.__proto__ || Object.getPrototypeOf(AutosizeInput)).call(this, props));

		_this.inputRef = function (el) {
			_this.input = el;
			if (typeof _this.props.inputRef === 'function') {
				_this.props.inputRef(el);
			}
		};

		_this.placeHolderSizerRef = function (el) {
			_this.placeHolderSizer = el;
		};

		_this.sizerRef = function (el) {
			_this.sizer = el;
		};

		_this.state = {
			inputWidth: props.minWidth,
			inputId: props.id || generateId()
		};
		return _this;
	}

	_createClass(AutosizeInput, [{
		key: 'componentDidMount',
		value: function componentDidMount() {
			this.mounted = true;
			this.copyInputStyles();
			this.updateInputWidth();
		}
	}, {
		key: 'componentWillReceiveProps',
		value: function componentWillReceiveProps(nextProps) {
			var id = nextProps.id;

			if (id !== this.props.id) {
				this.setState({ inputId: id || generateId() });
			}
		}
	}, {
		key: 'componentDidUpdate',
		value: function componentDidUpdate(prevProps, prevState) {
			if (prevState.inputWidth !== this.state.inputWidth) {
				if (typeof this.props.onAutosize === 'function') {
					this.props.onAutosize(this.state.inputWidth);
				}
			}
			this.updateInputWidth();
		}
	}, {
		key: 'componentWillUnmount',
		value: function componentWillUnmount() {
			this.mounted = false;
		}
	}, {
		key: 'copyInputStyles',
		value: function copyInputStyles() {
			if (!this.mounted || !window.getComputedStyle) {
				return;
			}
			var inputStyles = this.input && window.getComputedStyle(this.input);
			if (!inputStyles) {
				return;
			}
			copyStyles(inputStyles, this.sizer);
			if (this.placeHolderSizer) {
				copyStyles(inputStyles, this.placeHolderSizer);
			}
		}
	}, {
		key: 'updateInputWidth',
		value: function updateInputWidth() {
			if (!this.mounted || !this.sizer || typeof this.sizer.scrollWidth === 'undefined') {
				return;
			}
			var newInputWidth = void 0;
			if (this.props.placeholder && (!this.props.value || this.props.value && this.props.placeholderIsMinWidth)) {
				newInputWidth = Math.max(this.sizer.scrollWidth, this.placeHolderSizer.scrollWidth) + 2;
			} else {
				newInputWidth = this.sizer.scrollWidth + 2;
			}
			// add extraWidth to the detected width. for number types, this defaults to 16 to allow for the stepper UI
			var extraWidth = this.props.type === 'number' && this.props.extraWidth === undefined ? 16 : parseInt(this.props.extraWidth) || 0;
			newInputWidth += extraWidth;
			if (newInputWidth < this.props.minWidth) {
				newInputWidth = this.props.minWidth;
			}
			if (newInputWidth !== this.state.inputWidth) {
				this.setState({
					inputWidth: newInputWidth
				});
			}
		}
	}, {
		key: 'getInput',
		value: function getInput() {
			return this.input;
		}
	}, {
		key: 'focus',
		value: function focus() {
			this.input.focus();
		}
	}, {
		key: 'blur',
		value: function blur() {
			this.input.blur();
		}
	}, {
		key: 'select',
		value: function select() {
			this.input.select();
		}
	}, {
		key: 'renderStyles',
		value: function renderStyles() {
			// this method injects styles to hide IE's clear indicator, which messes
			// with input size detection. the stylesheet is only injected when the
			// browser is IE, and can also be disabled by the `injectStyles` prop.
			var injectStyles = this.props.injectStyles;

			return isIE && injectStyles ? _react2.default.createElement('style', { dangerouslySetInnerHTML: {
					__html: 'input#' + this.state.inputId + '::-ms-clear {display: none;}'
				} }) : null;
		}
	}, {
		key: 'render',
		value: function render() {
			var sizerValue = [this.props.defaultValue, this.props.value, ''].reduce(function (previousValue, currentValue) {
				if (previousValue !== null && previousValue !== undefined) {
					return previousValue;
				}
				return currentValue;
			});

			var wrapperStyle = _extends({}, this.props.style);
			if (!wrapperStyle.display) wrapperStyle.display = 'inline-block';

			var inputStyle = _extends({
				boxSizing: 'content-box',
				width: this.state.inputWidth + 'px'
			}, this.props.inputStyle);

			var inputProps = _objectWithoutProperties(this.props, []);

			cleanInputProps(inputProps);
			inputProps.className = this.props.inputClassName;
			inputProps.id = this.state.inputId;
			inputProps.style = inputStyle;

			return _react2.default.createElement(
				'div',
				{ className: this.props.className, style: wrapperStyle },
				this.renderStyles(),
				_react2.default.createElement('input', _extends({}, inputProps, { ref: this.inputRef })),
				_react2.default.createElement(
					'div',
					{ ref: this.sizerRef, style: sizerStyle },
					sizerValue
				),
				this.props.placeholder ? _react2.default.createElement(
					'div',
					{ ref: this.placeHolderSizerRef, style: sizerStyle },
					this.props.placeholder
				) : null
			);
		}
	}]);

	return AutosizeInput;
}(React__default.Component);

AutosizeInput.propTypes = {
	className: _propTypes2.default.string, // className for the outer element
	defaultValue: _propTypes2.default.any, // default field value
	extraWidth: _propTypes2.default.oneOfType([// additional width for input element
	_propTypes2.default.number, _propTypes2.default.string]),
	id: _propTypes2.default.string, // id to use for the input, can be set for consistent snapshots
	injectStyles: _propTypes2.default.bool, // inject the custom stylesheet to hide clear UI, defaults to true
	inputClassName: _propTypes2.default.string, // className for the input element
	inputRef: _propTypes2.default.func, // ref callback for the input element
	inputStyle: _propTypes2.default.object, // css styles for the input element
	minWidth: _propTypes2.default.oneOfType([// minimum width for input element
	_propTypes2.default.number, _propTypes2.default.string]),
	onAutosize: _propTypes2.default.func, // onAutosize handler: function(newWidth) {}
	onChange: _propTypes2.default.func, // onChange handler: function(event) {}
	placeholder: _propTypes2.default.string, // placeholder text
	placeholderIsMinWidth: _propTypes2.default.bool, // don't collapse size to less than the placeholder
	style: _propTypes2.default.object, // css styles for the outer element
	value: _propTypes2.default.any // field value
};
AutosizeInput.defaultProps = {
	minWidth: 1,
	injectStyles: true
};

exports.default = AutosizeInput;
});

var AutosizeInput = unwrapExports(AutosizeInput_1);

var arrowRenderer = function arrowRenderer(_ref) {
	var onMouseDown = _ref.onMouseDown;

	return React__default.createElement('span', {
		className: 'Select-arrow',
		onMouseDown: onMouseDown
	});
};

arrowRenderer.propTypes = {
	onMouseDown: propTypes.func
};

var clearRenderer = function clearRenderer() {
	return React__default.createElement('span', {
		className: 'Select-clear',
		dangerouslySetInnerHTML: { __html: '&times;' }
	});
};

var map = [{ 'base': 'A', 'letters': /[\u0041\u24B6\uFF21\u00C0\u00C1\u00C2\u1EA6\u1EA4\u1EAA\u1EA8\u00C3\u0100\u0102\u1EB0\u1EAE\u1EB4\u1EB2\u0226\u01E0\u00C4\u01DE\u1EA2\u00C5\u01FA\u01CD\u0200\u0202\u1EA0\u1EAC\u1EB6\u1E00\u0104\u023A\u2C6F]/g }, { 'base': 'AA', 'letters': /[\uA732]/g }, { 'base': 'AE', 'letters': /[\u00C6\u01FC\u01E2]/g }, { 'base': 'AO', 'letters': /[\uA734]/g }, { 'base': 'AU', 'letters': /[\uA736]/g }, { 'base': 'AV', 'letters': /[\uA738\uA73A]/g }, { 'base': 'AY', 'letters': /[\uA73C]/g }, { 'base': 'B', 'letters': /[\u0042\u24B7\uFF22\u1E02\u1E04\u1E06\u0243\u0182\u0181]/g }, { 'base': 'C', 'letters': /[\u0043\u24B8\uFF23\u0106\u0108\u010A\u010C\u00C7\u1E08\u0187\u023B\uA73E]/g }, { 'base': 'D', 'letters': /[\u0044\u24B9\uFF24\u1E0A\u010E\u1E0C\u1E10\u1E12\u1E0E\u0110\u018B\u018A\u0189\uA779]/g }, { 'base': 'DZ', 'letters': /[\u01F1\u01C4]/g }, { 'base': 'Dz', 'letters': /[\u01F2\u01C5]/g }, { 'base': 'E', 'letters': /[\u0045\u24BA\uFF25\u00C8\u00C9\u00CA\u1EC0\u1EBE\u1EC4\u1EC2\u1EBC\u0112\u1E14\u1E16\u0114\u0116\u00CB\u1EBA\u011A\u0204\u0206\u1EB8\u1EC6\u0228\u1E1C\u0118\u1E18\u1E1A\u0190\u018E]/g }, { 'base': 'F', 'letters': /[\u0046\u24BB\uFF26\u1E1E\u0191\uA77B]/g }, { 'base': 'G', 'letters': /[\u0047\u24BC\uFF27\u01F4\u011C\u1E20\u011E\u0120\u01E6\u0122\u01E4\u0193\uA7A0\uA77D\uA77E]/g }, { 'base': 'H', 'letters': /[\u0048\u24BD\uFF28\u0124\u1E22\u1E26\u021E\u1E24\u1E28\u1E2A\u0126\u2C67\u2C75\uA78D]/g }, { 'base': 'I', 'letters': /[\u0049\u24BE\uFF29\u00CC\u00CD\u00CE\u0128\u012A\u012C\u0130\u00CF\u1E2E\u1EC8\u01CF\u0208\u020A\u1ECA\u012E\u1E2C\u0197]/g }, { 'base': 'J', 'letters': /[\u004A\u24BF\uFF2A\u0134\u0248]/g }, { 'base': 'K', 'letters': /[\u004B\u24C0\uFF2B\u1E30\u01E8\u1E32\u0136\u1E34\u0198\u2C69\uA740\uA742\uA744\uA7A2]/g }, { 'base': 'L', 'letters': /[\u004C\u24C1\uFF2C\u013F\u0139\u013D\u1E36\u1E38\u013B\u1E3C\u1E3A\u0141\u023D\u2C62\u2C60\uA748\uA746\uA780]/g }, { 'base': 'LJ', 'letters': /[\u01C7]/g }, { 'base': 'Lj', 'letters': /[\u01C8]/g }, { 'base': 'M', 'letters': /[\u004D\u24C2\uFF2D\u1E3E\u1E40\u1E42\u2C6E\u019C]/g }, { 'base': 'N', 'letters': /[\u004E\u24C3\uFF2E\u01F8\u0143\u00D1\u1E44\u0147\u1E46\u0145\u1E4A\u1E48\u0220\u019D\uA790\uA7A4]/g }, { 'base': 'NJ', 'letters': /[\u01CA]/g }, { 'base': 'Nj', 'letters': /[\u01CB]/g }, { 'base': 'O', 'letters': /[\u004F\u24C4\uFF2F\u00D2\u00D3\u00D4\u1ED2\u1ED0\u1ED6\u1ED4\u00D5\u1E4C\u022C\u1E4E\u014C\u1E50\u1E52\u014E\u022E\u0230\u00D6\u022A\u1ECE\u0150\u01D1\u020C\u020E\u01A0\u1EDC\u1EDA\u1EE0\u1EDE\u1EE2\u1ECC\u1ED8\u01EA\u01EC\u00D8\u01FE\u0186\u019F\uA74A\uA74C]/g }, { 'base': 'OI', 'letters': /[\u01A2]/g }, { 'base': 'OO', 'letters': /[\uA74E]/g }, { 'base': 'OU', 'letters': /[\u0222]/g }, { 'base': 'P', 'letters': /[\u0050\u24C5\uFF30\u1E54\u1E56\u01A4\u2C63\uA750\uA752\uA754]/g }, { 'base': 'Q', 'letters': /[\u0051\u24C6\uFF31\uA756\uA758\u024A]/g }, { 'base': 'R', 'letters': /[\u0052\u24C7\uFF32\u0154\u1E58\u0158\u0210\u0212\u1E5A\u1E5C\u0156\u1E5E\u024C\u2C64\uA75A\uA7A6\uA782]/g }, { 'base': 'S', 'letters': /[\u0053\u24C8\uFF33\u1E9E\u015A\u1E64\u015C\u1E60\u0160\u1E66\u1E62\u1E68\u0218\u015E\u2C7E\uA7A8\uA784]/g }, { 'base': 'T', 'letters': /[\u0054\u24C9\uFF34\u1E6A\u0164\u1E6C\u021A\u0162\u1E70\u1E6E\u0166\u01AC\u01AE\u023E\uA786]/g }, { 'base': 'TZ', 'letters': /[\uA728]/g }, { 'base': 'U', 'letters': /[\u0055\u24CA\uFF35\u00D9\u00DA\u00DB\u0168\u1E78\u016A\u1E7A\u016C\u00DC\u01DB\u01D7\u01D5\u01D9\u1EE6\u016E\u0170\u01D3\u0214\u0216\u01AF\u1EEA\u1EE8\u1EEE\u1EEC\u1EF0\u1EE4\u1E72\u0172\u1E76\u1E74\u0244]/g }, { 'base': 'V', 'letters': /[\u0056\u24CB\uFF36\u1E7C\u1E7E\u01B2\uA75E\u0245]/g }, { 'base': 'VY', 'letters': /[\uA760]/g }, { 'base': 'W', 'letters': /[\u0057\u24CC\uFF37\u1E80\u1E82\u0174\u1E86\u1E84\u1E88\u2C72]/g }, { 'base': 'X', 'letters': /[\u0058\u24CD\uFF38\u1E8A\u1E8C]/g }, { 'base': 'Y', 'letters': /[\u0059\u24CE\uFF39\u1EF2\u00DD\u0176\u1EF8\u0232\u1E8E\u0178\u1EF6\u1EF4\u01B3\u024E\u1EFE]/g }, { 'base': 'Z', 'letters': /[\u005A\u24CF\uFF3A\u0179\u1E90\u017B\u017D\u1E92\u1E94\u01B5\u0224\u2C7F\u2C6B\uA762]/g }, { 'base': 'a', 'letters': /[\u0061\u24D0\uFF41\u1E9A\u00E0\u00E1\u00E2\u1EA7\u1EA5\u1EAB\u1EA9\u00E3\u0101\u0103\u1EB1\u1EAF\u1EB5\u1EB3\u0227\u01E1\u00E4\u01DF\u1EA3\u00E5\u01FB\u01CE\u0201\u0203\u1EA1\u1EAD\u1EB7\u1E01\u0105\u2C65\u0250]/g }, { 'base': 'aa', 'letters': /[\uA733]/g }, { 'base': 'ae', 'letters': /[\u00E6\u01FD\u01E3]/g }, { 'base': 'ao', 'letters': /[\uA735]/g }, { 'base': 'au', 'letters': /[\uA737]/g }, { 'base': 'av', 'letters': /[\uA739\uA73B]/g }, { 'base': 'ay', 'letters': /[\uA73D]/g }, { 'base': 'b', 'letters': /[\u0062\u24D1\uFF42\u1E03\u1E05\u1E07\u0180\u0183\u0253]/g }, { 'base': 'c', 'letters': /[\u0063\u24D2\uFF43\u0107\u0109\u010B\u010D\u00E7\u1E09\u0188\u023C\uA73F\u2184]/g }, { 'base': 'd', 'letters': /[\u0064\u24D3\uFF44\u1E0B\u010F\u1E0D\u1E11\u1E13\u1E0F\u0111\u018C\u0256\u0257\uA77A]/g }, { 'base': 'dz', 'letters': /[\u01F3\u01C6]/g }, { 'base': 'e', 'letters': /[\u0065\u24D4\uFF45\u00E8\u00E9\u00EA\u1EC1\u1EBF\u1EC5\u1EC3\u1EBD\u0113\u1E15\u1E17\u0115\u0117\u00EB\u1EBB\u011B\u0205\u0207\u1EB9\u1EC7\u0229\u1E1D\u0119\u1E19\u1E1B\u0247\u025B\u01DD]/g }, { 'base': 'f', 'letters': /[\u0066\u24D5\uFF46\u1E1F\u0192\uA77C]/g }, { 'base': 'g', 'letters': /[\u0067\u24D6\uFF47\u01F5\u011D\u1E21\u011F\u0121\u01E7\u0123\u01E5\u0260\uA7A1\u1D79\uA77F]/g }, { 'base': 'h', 'letters': /[\u0068\u24D7\uFF48\u0125\u1E23\u1E27\u021F\u1E25\u1E29\u1E2B\u1E96\u0127\u2C68\u2C76\u0265]/g }, { 'base': 'hv', 'letters': /[\u0195]/g }, { 'base': 'i', 'letters': /[\u0069\u24D8\uFF49\u00EC\u00ED\u00EE\u0129\u012B\u012D\u00EF\u1E2F\u1EC9\u01D0\u0209\u020B\u1ECB\u012F\u1E2D\u0268\u0131]/g }, { 'base': 'j', 'letters': /[\u006A\u24D9\uFF4A\u0135\u01F0\u0249]/g }, { 'base': 'k', 'letters': /[\u006B\u24DA\uFF4B\u1E31\u01E9\u1E33\u0137\u1E35\u0199\u2C6A\uA741\uA743\uA745\uA7A3]/g }, { 'base': 'l', 'letters': /[\u006C\u24DB\uFF4C\u0140\u013A\u013E\u1E37\u1E39\u013C\u1E3D\u1E3B\u017F\u0142\u019A\u026B\u2C61\uA749\uA781\uA747]/g }, { 'base': 'lj', 'letters': /[\u01C9]/g }, { 'base': 'm', 'letters': /[\u006D\u24DC\uFF4D\u1E3F\u1E41\u1E43\u0271\u026F]/g }, { 'base': 'n', 'letters': /[\u006E\u24DD\uFF4E\u01F9\u0144\u00F1\u1E45\u0148\u1E47\u0146\u1E4B\u1E49\u019E\u0272\u0149\uA791\uA7A5]/g }, { 'base': 'nj', 'letters': /[\u01CC]/g }, { 'base': 'o', 'letters': /[\u006F\u24DE\uFF4F\u00F2\u00F3\u00F4\u1ED3\u1ED1\u1ED7\u1ED5\u00F5\u1E4D\u022D\u1E4F\u014D\u1E51\u1E53\u014F\u022F\u0231\u00F6\u022B\u1ECF\u0151\u01D2\u020D\u020F\u01A1\u1EDD\u1EDB\u1EE1\u1EDF\u1EE3\u1ECD\u1ED9\u01EB\u01ED\u00F8\u01FF\u0254\uA74B\uA74D\u0275]/g }, { 'base': 'oi', 'letters': /[\u01A3]/g }, { 'base': 'ou', 'letters': /[\u0223]/g }, { 'base': 'oo', 'letters': /[\uA74F]/g }, { 'base': 'p', 'letters': /[\u0070\u24DF\uFF50\u1E55\u1E57\u01A5\u1D7D\uA751\uA753\uA755]/g }, { 'base': 'q', 'letters': /[\u0071\u24E0\uFF51\u024B\uA757\uA759]/g }, { 'base': 'r', 'letters': /[\u0072\u24E1\uFF52\u0155\u1E59\u0159\u0211\u0213\u1E5B\u1E5D\u0157\u1E5F\u024D\u027D\uA75B\uA7A7\uA783]/g }, { 'base': 's', 'letters': /[\u0073\u24E2\uFF53\u00DF\u015B\u1E65\u015D\u1E61\u0161\u1E67\u1E63\u1E69\u0219\u015F\u023F\uA7A9\uA785\u1E9B]/g }, { 'base': 't', 'letters': /[\u0074\u24E3\uFF54\u1E6B\u1E97\u0165\u1E6D\u021B\u0163\u1E71\u1E6F\u0167\u01AD\u0288\u2C66\uA787]/g }, { 'base': 'tz', 'letters': /[\uA729]/g }, { 'base': 'u', 'letters': /[\u0075\u24E4\uFF55\u00F9\u00FA\u00FB\u0169\u1E79\u016B\u1E7B\u016D\u00FC\u01DC\u01D8\u01D6\u01DA\u1EE7\u016F\u0171\u01D4\u0215\u0217\u01B0\u1EEB\u1EE9\u1EEF\u1EED\u1EF1\u1EE5\u1E73\u0173\u1E77\u1E75\u0289]/g }, { 'base': 'v', 'letters': /[\u0076\u24E5\uFF56\u1E7D\u1E7F\u028B\uA75F\u028C]/g }, { 'base': 'vy', 'letters': /[\uA761]/g }, { 'base': 'w', 'letters': /[\u0077\u24E6\uFF57\u1E81\u1E83\u0175\u1E87\u1E85\u1E98\u1E89\u2C73]/g }, { 'base': 'x', 'letters': /[\u0078\u24E7\uFF58\u1E8B\u1E8D]/g }, { 'base': 'y', 'letters': /[\u0079\u24E8\uFF59\u1EF3\u00FD\u0177\u1EF9\u0233\u1E8F\u00FF\u1EF7\u1E99\u1EF5\u01B4\u024F\u1EFF]/g }, { 'base': 'z', 'letters': /[\u007A\u24E9\uFF5A\u017A\u1E91\u017C\u017E\u1E93\u1E95\u01B6\u0225\u0240\u2C6C\uA763]/g }];

var stripDiacritics = function stripDiacritics(str) {
	for (var i = 0; i < map.length; i++) {
		str = str.replace(map[i].letters, map[i].base);
	}
	return str;
};

var trim = function trim(str) {
  return str.replace(/^\s+|\s+$/g, '');
};

var isValid = function isValid(value) {
	return typeof value !== 'undefined' && value !== null && value !== '';
};

var filterOptions = function filterOptions(options, filterValue, excludeOptions, props) {
	if (props.ignoreAccents) {
		filterValue = stripDiacritics(filterValue);
	}

	if (props.ignoreCase) {
		filterValue = filterValue.toLowerCase();
	}

	if (props.trimFilter) {
		filterValue = trim(filterValue);
	}

	if (excludeOptions) excludeOptions = excludeOptions.map(function (i) {
		return i[props.valueKey];
	});

	return options.filter(function (option) {
		if (excludeOptions && excludeOptions.indexOf(option[props.valueKey]) > -1) return false;
		if (props.filterOption) return props.filterOption.call(undefined, option, filterValue);
		if (!filterValue) return true;

		var value = option[props.valueKey];
		var label = option[props.labelKey];
		var hasValue = isValid(value);
		var hasLabel = isValid(label);

		if (!hasValue && !hasLabel) {
			return false;
		}

		var valueTest = hasValue ? String(value) : null;
		var labelTest = hasLabel ? String(label) : null;

		if (props.ignoreAccents) {
			if (valueTest && props.matchProp !== 'label') valueTest = stripDiacritics(valueTest);
			if (labelTest && props.matchProp !== 'value') labelTest = stripDiacritics(labelTest);
		}

		if (props.ignoreCase) {
			if (valueTest && props.matchProp !== 'label') valueTest = valueTest.toLowerCase();
			if (labelTest && props.matchProp !== 'value') labelTest = labelTest.toLowerCase();
		}

		return props.matchPos === 'start' ? valueTest && props.matchProp !== 'label' && valueTest.substr(0, filterValue.length) === filterValue || labelTest && props.matchProp !== 'value' && labelTest.substr(0, filterValue.length) === filterValue : valueTest && props.matchProp !== 'label' && valueTest.indexOf(filterValue) >= 0 || labelTest && props.matchProp !== 'value' && labelTest.indexOf(filterValue) >= 0;
	});
};

var menuRenderer = function menuRenderer(_ref) {
	var focusedOption = _ref.focusedOption,
	    focusOption = _ref.focusOption,
	    inputValue = _ref.inputValue,
	    instancePrefix = _ref.instancePrefix,
	    onFocus = _ref.onFocus,
	    onOptionRef = _ref.onOptionRef,
	    onSelect = _ref.onSelect,
	    optionClassName = _ref.optionClassName,
	    optionComponent = _ref.optionComponent,
	    optionRenderer = _ref.optionRenderer,
	    options = _ref.options,
	    removeValue = _ref.removeValue,
	    selectValue = _ref.selectValue,
	    valueArray = _ref.valueArray,
	    valueKey = _ref.valueKey;

	var Option = optionComponent;

	return options.map(function (option, i) {
		var isSelected = valueArray && valueArray.some(function (x) {
			return x[valueKey] === option[valueKey];
		});
		var isFocused = option === focusedOption;
		var optionClass = cx(optionClassName, {
			'Select-option': true,
			'is-selected': isSelected,
			'is-focused': isFocused,
			'is-disabled': option.disabled
		});

		return React__default.createElement(
			Option,
			{
				className: optionClass,
				focusOption: focusOption,
				inputValue: inputValue,
				instancePrefix: instancePrefix,
				isDisabled: option.disabled,
				isFocused: isFocused,
				isSelected: isSelected,
				key: 'option-' + i + '-' + option[valueKey],
				onFocus: onFocus,
				onSelect: onSelect,
				option: option,
				optionIndex: i,
				ref: function ref(_ref2) {
					onOptionRef(_ref2, isFocused);
				},
				removeValue: removeValue,
				selectValue: selectValue
			},
			optionRenderer(option, i, inputValue)
		);
	});
};

menuRenderer.propTypes = {
	focusOption: propTypes.func,
	focusedOption: propTypes.object,
	inputValue: propTypes.string,
	instancePrefix: propTypes.string,
	onFocus: propTypes.func,
	onOptionRef: propTypes.func,
	onSelect: propTypes.func,
	optionClassName: propTypes.string,
	optionComponent: propTypes.func,
	optionRenderer: propTypes.func,
	options: propTypes.array,
	removeValue: propTypes.func,
	selectValue: propTypes.func,
	valueArray: propTypes.array,
	valueKey: propTypes.string
};

var blockEvent = (function (event) {
	event.preventDefault();
	event.stopPropagation();
	if (event.target.tagName !== 'A' || !('href' in event.target)) {
		return;
	}
	if (event.target.target) {
		window.open(event.target.href, event.target.target);
	} else {
		window.location.href = event.target.href;
	}
});

var _typeof = typeof Symbol === "function" && typeof Symbol.iterator === "symbol" ? function (obj) {
  return typeof obj;
} : function (obj) {
  return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
};





var classCallCheck = function (instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
};

var createClass = function () {
  function defineProperties(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i];
      descriptor.enumerable = descriptor.enumerable || false;
      descriptor.configurable = true;
      if ("value" in descriptor) descriptor.writable = true;
      Object.defineProperty(target, descriptor.key, descriptor);
    }
  }

  return function (Constructor, protoProps, staticProps) {
    if (protoProps) defineProperties(Constructor.prototype, protoProps);
    if (staticProps) defineProperties(Constructor, staticProps);
    return Constructor;
  };
}();





var defineProperty = function (obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value: value,
      enumerable: true,
      configurable: true,
      writable: true
    });
  } else {
    obj[key] = value;
  }

  return obj;
};

var _extends = Object.assign || function (target) {
  for (var i = 1; i < arguments.length; i++) {
    var source = arguments[i];

    for (var key in source) {
      if (Object.prototype.hasOwnProperty.call(source, key)) {
        target[key] = source[key];
      }
    }
  }

  return target;
};



var inherits = function (subClass, superClass) {
  if (typeof superClass !== "function" && superClass !== null) {
    throw new TypeError("Super expression must either be null or a function, not " + typeof superClass);
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      enumerable: false,
      writable: true,
      configurable: true
    }
  });
  if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass;
};









var objectWithoutProperties = function (obj, keys) {
  var target = {};

  for (var i in obj) {
    if (keys.indexOf(i) >= 0) continue;
    if (!Object.prototype.hasOwnProperty.call(obj, i)) continue;
    target[i] = obj[i];
  }

  return target;
};

var possibleConstructorReturn = function (self, call) {
  if (!self) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return call && (typeof call === "object" || typeof call === "function") ? call : self;
};

var Option = function (_React$Component) {
	inherits(Option, _React$Component);

	function Option(props) {
		classCallCheck(this, Option);

		var _this = possibleConstructorReturn(this, (Option.__proto__ || Object.getPrototypeOf(Option)).call(this, props));

		_this.handleMouseDown = _this.handleMouseDown.bind(_this);
		_this.handleMouseEnter = _this.handleMouseEnter.bind(_this);
		_this.handleMouseMove = _this.handleMouseMove.bind(_this);
		_this.handleTouchStart = _this.handleTouchStart.bind(_this);
		_this.handleTouchEnd = _this.handleTouchEnd.bind(_this);
		_this.handleTouchMove = _this.handleTouchMove.bind(_this);
		_this.onFocus = _this.onFocus.bind(_this);
		return _this;
	}

	createClass(Option, [{
		key: 'handleMouseDown',
		value: function handleMouseDown(event) {
			event.preventDefault();
			event.stopPropagation();
			this.props.onSelect(this.props.option, event);
		}
	}, {
		key: 'handleMouseEnter',
		value: function handleMouseEnter(event) {
			this.onFocus(event);
		}
	}, {
		key: 'handleMouseMove',
		value: function handleMouseMove(event) {
			this.onFocus(event);
		}
	}, {
		key: 'handleTouchEnd',
		value: function handleTouchEnd(event) {
			// Check if the view is being dragged, In this case
			// we don't want to fire the click event (because the user only wants to scroll)
			if (this.dragging) return;

			this.handleMouseDown(event);
		}
	}, {
		key: 'handleTouchMove',
		value: function handleTouchMove() {
			// Set a flag that the view is being dragged
			this.dragging = true;
		}
	}, {
		key: 'handleTouchStart',
		value: function handleTouchStart() {
			// Set a flag that the view is not being dragged
			this.dragging = false;
		}
	}, {
		key: 'onFocus',
		value: function onFocus(event) {
			if (!this.props.isFocused) {
				this.props.onFocus(this.props.option, event);
			}
		}
	}, {
		key: 'render',
		value: function render() {
			var _props = this.props,
			    option = _props.option,
			    instancePrefix = _props.instancePrefix,
			    optionIndex = _props.optionIndex;

			var className = cx(this.props.className, option.className);

			return option.disabled ? React__default.createElement(
				'div',
				{ className: className,
					onMouseDown: blockEvent,
					onClick: blockEvent },
				this.props.children
			) : React__default.createElement(
				'div',
				{ className: className,
					style: option.style,
					role: 'option',
					'aria-label': option.label,
					onMouseDown: this.handleMouseDown,
					onMouseEnter: this.handleMouseEnter,
					onMouseMove: this.handleMouseMove,
					onTouchStart: this.handleTouchStart,
					onTouchMove: this.handleTouchMove,
					onTouchEnd: this.handleTouchEnd,
					id: instancePrefix + '-option-' + optionIndex,
					title: option.title },
				this.props.children
			);
		}
	}]);
	return Option;
}(React__default.Component);

Option.propTypes = {
	children: propTypes.node,
	className: propTypes.string, // className (based on mouse position)
	instancePrefix: propTypes.string.isRequired, // unique prefix for the ids (used for aria)
	isDisabled: propTypes.bool, // the option is disabled
	isFocused: propTypes.bool, // the option is focused
	isSelected: propTypes.bool, // the option is selected
	onFocus: propTypes.func, // method to handle mouseEnter on option element
	onSelect: propTypes.func, // method to handle click on option element
	onUnfocus: propTypes.func, // method to handle mouseLeave on option element
	option: propTypes.object.isRequired, // object that is base for that option
	optionIndex: propTypes.number // index of the option, used to generate unique ids for aria
};

var Value = function (_React$Component) {
	inherits(Value, _React$Component);

	function Value(props) {
		classCallCheck(this, Value);

		var _this = possibleConstructorReturn(this, (Value.__proto__ || Object.getPrototypeOf(Value)).call(this, props));

		_this.handleMouseDown = _this.handleMouseDown.bind(_this);
		_this.onRemove = _this.onRemove.bind(_this);
		_this.handleTouchEndRemove = _this.handleTouchEndRemove.bind(_this);
		_this.handleTouchMove = _this.handleTouchMove.bind(_this);
		_this.handleTouchStart = _this.handleTouchStart.bind(_this);
		return _this;
	}

	createClass(Value, [{
		key: 'handleMouseDown',
		value: function handleMouseDown(event) {
			if (event.type === 'mousedown' && event.button !== 0) {
				return;
			}
			if (this.props.onClick) {
				event.stopPropagation();
				this.props.onClick(this.props.value, event);
				return;
			}
			if (this.props.value.href) {
				event.stopPropagation();
			}
		}
	}, {
		key: 'onRemove',
		value: function onRemove(event) {
			event.preventDefault();
			event.stopPropagation();
			this.props.onRemove(this.props.value);
		}
	}, {
		key: 'handleTouchEndRemove',
		value: function handleTouchEndRemove(event) {
			// Check if the view is being dragged, In this case
			// we don't want to fire the click event (because the user only wants to scroll)
			if (this.dragging) return;

			// Fire the mouse events
			this.onRemove(event);
		}
	}, {
		key: 'handleTouchMove',
		value: function handleTouchMove() {
			// Set a flag that the view is being dragged
			this.dragging = true;
		}
	}, {
		key: 'handleTouchStart',
		value: function handleTouchStart() {
			// Set a flag that the view is not being dragged
			this.dragging = false;
		}
	}, {
		key: 'renderRemoveIcon',
		value: function renderRemoveIcon() {
			if (this.props.disabled || !this.props.onRemove) return;
			return React__default.createElement(
				'span',
				{ className: 'Select-value-icon',
					'aria-hidden': 'true',
					onMouseDown: this.onRemove,
					onTouchEnd: this.handleTouchEndRemove,
					onTouchStart: this.handleTouchStart,
					onTouchMove: this.handleTouchMove },
				'\xD7'
			);
		}
	}, {
		key: 'renderLabel',
		value: function renderLabel() {
			var className = 'Select-value-label';
			return this.props.onClick || this.props.value.href ? React__default.createElement(
				'a',
				{ className: className, href: this.props.value.href, target: this.props.value.target, onMouseDown: this.handleMouseDown, onTouchEnd: this.handleMouseDown },
				this.props.children
			) : React__default.createElement(
				'span',
				{ className: className, role: 'option', 'aria-selected': 'true', id: this.props.id },
				this.props.children
			);
		}
	}, {
		key: 'render',
		value: function render() {
			return React__default.createElement(
				'div',
				{ className: cx('Select-value', this.props.value.disabled ? 'Select-value-disabled' : '', this.props.value.className),
					style: this.props.value.style,
					title: this.props.value.title
				},
				this.renderRemoveIcon(),
				this.renderLabel()
			);
		}
	}]);
	return Value;
}(React__default.Component);

Value.propTypes = {
	children: propTypes.node,
	disabled: propTypes.bool, // disabled prop passed to ReactSelect
	id: propTypes.string, // Unique id for the value - used for aria
	onClick: propTypes.func, // method to handle click on value label
	onRemove: propTypes.func, // method to handle removal of the value
	value: propTypes.object.isRequired // the option object for this value
};

/*!
  Copyright (c) 2018 Jed Watson.
  Licensed under the MIT License (MIT), see
  http://jedwatson.github.io/react-select
*/
var stringifyValue = function stringifyValue(value) {
	return typeof value === 'string' ? value : value !== null && JSON.stringify(value) || '';
};

var stringOrNode = propTypes.oneOfType([propTypes.string, propTypes.node]);
var stringOrNumber = propTypes.oneOfType([propTypes.string, propTypes.number]);

var instanceId = 1;

var shouldShowValue = function shouldShowValue(state, props) {
	var inputValue = state.inputValue,
	    isPseudoFocused = state.isPseudoFocused,
	    isFocused = state.isFocused;
	var onSelectResetsInput = props.onSelectResetsInput;


	if (!inputValue) return true;

	if (!onSelectResetsInput) {
		return !(!isFocused && isPseudoFocused || isFocused && !isPseudoFocused);
	}

	return false;
};

var shouldShowPlaceholder = function shouldShowPlaceholder(state, props, isOpen) {
	var inputValue = state.inputValue,
	    isPseudoFocused = state.isPseudoFocused,
	    isFocused = state.isFocused;
	var onSelectResetsInput = props.onSelectResetsInput;


	return !inputValue || !onSelectResetsInput && !isOpen && !isPseudoFocused && !isFocused;
};

/**
 * Retrieve a value from the given options and valueKey
 * @param {String|Number|Array} value	- the selected value(s)
 * @param {Object}		 props	- the Select component's props (or nextProps)
 */
var expandValue = function expandValue(value, props) {
	var valueType = typeof value === 'undefined' ? 'undefined' : _typeof(value);
	if (valueType !== 'string' && valueType !== 'number' && valueType !== 'boolean') return value;
	var options = props.options,
	    valueKey = props.valueKey;

	if (!options) return;
	for (var i = 0; i < options.length; i++) {
		if (String(options[i][valueKey]) === String(value)) return options[i];
	}
};

var handleRequired = function handleRequired(value, multi) {
	if (!value) return true;
	return multi ? value.length === 0 : Object.keys(value).length === 0;
};

var Select$1 = function (_React$Component) {
	inherits(Select, _React$Component);

	function Select(props) {
		classCallCheck(this, Select);

		var _this = possibleConstructorReturn(this, (Select.__proto__ || Object.getPrototypeOf(Select)).call(this, props));

		['clearValue', 'focusOption', 'getOptionLabel', 'handleInputBlur', 'handleInputChange', 'handleInputFocus', 'handleInputValueChange', 'handleKeyDown', 'handleMenuScroll', 'handleMouseDown', 'handleMouseDownOnArrow', 'handleMouseDownOnMenu', 'handleTouchEnd', 'handleTouchEndClearValue', 'handleTouchMove', 'handleTouchOutside', 'handleTouchStart', 'handleValueClick', 'onOptionRef', 'removeValue', 'selectValue'].forEach(function (fn) {
			return _this[fn] = _this[fn].bind(_this);
		});

		_this.state = {
			inputValue: '',
			isFocused: false,
			isOpen: false,
			isPseudoFocused: false,
			required: false
		};
		return _this;
	}

	createClass(Select, [{
		key: 'componentWillMount',
		value: function componentWillMount() {
			this._instancePrefix = 'react-select-' + (this.props.instanceId || ++instanceId) + '-';
			var valueArray = this.getValueArray(this.props.value);

			if (this.props.required) {
				this.setState({
					required: handleRequired(valueArray[0], this.props.multi)
				});
			}
		}
	}, {
		key: 'componentDidMount',
		value: function componentDidMount() {
			if (typeof this.props.autofocus !== 'undefined' && typeof console !== 'undefined') {
				console.warn('Warning: The autofocus prop has changed to autoFocus, support will be removed after react-select@1.0');
			}
			if (this.props.autoFocus || this.props.autofocus) {
				this.focus();
			}
		}
	}, {
		key: 'componentWillReceiveProps',
		value: function componentWillReceiveProps(nextProps) {
			var valueArray = this.getValueArray(nextProps.value, nextProps);

			if (nextProps.required) {
				this.setState({
					required: handleRequired(valueArray[0], nextProps.multi)
				});
			} else if (this.props.required) {
				// Used to be required but it's not any more
				this.setState({ required: false });
			}

			if (this.state.inputValue && this.props.value !== nextProps.value && nextProps.onSelectResetsInput) {
				this.setState({ inputValue: this.handleInputValueChange('') });
			}
		}
	}, {
		key: 'componentDidUpdate',
		value: function componentDidUpdate(prevProps, prevState) {
			// focus to the selected option
			if (this.menu && this.focused && this.state.isOpen && !this.hasScrolledToOption) {
				var focusedOptionNode = reactDom.findDOMNode(this.focused);
				var menuNode = reactDom.findDOMNode(this.menu);

				var scrollTop = menuNode.scrollTop;
				var scrollBottom = scrollTop + menuNode.offsetHeight;
				var optionTop = focusedOptionNode.offsetTop;
				var optionBottom = optionTop + focusedOptionNode.offsetHeight;

				if (scrollTop > optionTop || scrollBottom < optionBottom) {
					menuNode.scrollTop = focusedOptionNode.offsetTop;
				}

				// We still set hasScrolledToOption to true even if we didn't
				// actually need to scroll, as we've still confirmed that the
				// option is in view.
				this.hasScrolledToOption = true;
			} else if (!this.state.isOpen) {
				this.hasScrolledToOption = false;
			}

			if (this._scrollToFocusedOptionOnUpdate && this.focused && this.menu) {
				this._scrollToFocusedOptionOnUpdate = false;
				var focusedDOM = reactDom.findDOMNode(this.focused);
				var menuDOM = reactDom.findDOMNode(this.menu);
				var focusedRect = focusedDOM.getBoundingClientRect();
				var menuRect = menuDOM.getBoundingClientRect();
				if (focusedRect.bottom > menuRect.bottom) {
					menuDOM.scrollTop = focusedDOM.offsetTop + focusedDOM.clientHeight - menuDOM.offsetHeight;
				} else if (focusedRect.top < menuRect.top) {
					menuDOM.scrollTop = focusedDOM.offsetTop;
				}
			}
			if (this.props.scrollMenuIntoView && this.menuContainer) {
				var menuContainerRect = this.menuContainer.getBoundingClientRect();
				if (window.innerHeight < menuContainerRect.bottom + this.props.menuBuffer) {
					window.scrollBy(0, menuContainerRect.bottom + this.props.menuBuffer - window.innerHeight);
				}
			}
			if (prevProps.disabled !== this.props.disabled) {
				this.setState({ isFocused: false }); // eslint-disable-line react/no-did-update-set-state
				this.closeMenu();
			}
			if (prevState.isOpen !== this.state.isOpen) {
				this.toggleTouchOutsideEvent(this.state.isOpen);
				var handler = this.state.isOpen ? this.props.onOpen : this.props.onClose;
				handler && handler();
			}
		}
	}, {
		key: 'componentWillUnmount',
		value: function componentWillUnmount() {
			this.toggleTouchOutsideEvent(false);
		}
	}, {
		key: 'toggleTouchOutsideEvent',
		value: function toggleTouchOutsideEvent(enabled) {
			var eventTogglerName = enabled ? document.addEventListener ? 'addEventListener' : 'attachEvent' : document.removeEventListener ? 'removeEventListener' : 'detachEvent';
			var pref = document.addEventListener ? '' : 'on';

			document[eventTogglerName](pref + 'touchstart', this.handleTouchOutside);
			document[eventTogglerName](pref + 'mousedown', this.handleTouchOutside);
		}
	}, {
		key: 'handleTouchOutside',
		value: function handleTouchOutside(event) {
			// handle touch outside on ios to dismiss menu
			if (this.wrapper && !this.wrapper.contains(event.target)) {
				this.closeMenu();
			}
		}
	}, {
		key: 'focus',
		value: function focus() {
			if (!this.input) return;
			this.input.focus();
		}
	}, {
		key: 'blurInput',
		value: function blurInput() {
			if (!this.input) return;
			this.input.blur();
		}
	}, {
		key: 'handleTouchMove',
		value: function handleTouchMove() {
			// Set a flag that the view is being dragged
			this.dragging = true;
		}
	}, {
		key: 'handleTouchStart',
		value: function handleTouchStart() {
			// Set a flag that the view is not being dragged
			this.dragging = false;
		}
	}, {
		key: 'handleTouchEnd',
		value: function handleTouchEnd(event) {
			// Check if the view is being dragged, In this case
			// we don't want to fire the click event (because the user only wants to scroll)
			if (this.dragging) return;

			// Fire the mouse events
			this.handleMouseDown(event);
		}
	}, {
		key: 'handleTouchEndClearValue',
		value: function handleTouchEndClearValue(event) {
			// Check if the view is being dragged, In this case
			// we don't want to fire the click event (because the user only wants to scroll)
			if (this.dragging) return;

			// Clear the value
			this.clearValue(event);
		}
	}, {
		key: 'handleMouseDown',
		value: function handleMouseDown(event) {
			// if the event was triggered by a mousedown and not the primary
			// button, or if the component is disabled, ignore it.
			if (this.props.disabled || event.type === 'mousedown' && event.button !== 0) {
				return;
			}

			if (event.target.tagName === 'INPUT') {
				if (!this.state.isFocused) {
					this._openAfterFocus = this.props.openOnClick;
					this.focus();
				} else if (!this.state.isOpen) {
					this.setState({
						isOpen: true,
						isPseudoFocused: false,
						focusedOption: null
					});
				}

				return;
			}

			// prevent default event handlers
			event.preventDefault();

			// for the non-searchable select, toggle the menu
			if (!this.props.searchable) {
				// This code means that if a select is searchable, onClick the options menu will not appear, only on subsequent click will it open.
				this.focus();
				return this.setState({
					isOpen: !this.state.isOpen,
					focusedOption: null
				});
			}

			if (this.state.isFocused) {
				// On iOS, we can get into a state where we think the input is focused but it isn't really,
				// since iOS ignores programmatic calls to input.focus() that weren't triggered by a click event.
				// Call focus() again here to be safe.
				this.focus();

				var input = this.input;
				var toOpen = true;

				if (typeof input.getInput === 'function') {
					// Get the actual DOM input if the ref is an <AutosizeInput /> component
					input = input.getInput();
				}

				// clears the value so that the cursor will be at the end of input when the component re-renders
				input.value = '';

				if (this._focusAfterClear) {
					toOpen = false;
					this._focusAfterClear = false;
				}

				// if the input is focused, ensure the menu is open
				this.setState({
					isOpen: toOpen,
					isPseudoFocused: false,
					focusedOption: null
				});
			} else {
				// otherwise, focus the input and open the menu
				this._openAfterFocus = this.props.openOnClick;
				this.focus();
				this.setState({ focusedOption: null });
			}
		}
	}, {
		key: 'handleMouseDownOnArrow',
		value: function handleMouseDownOnArrow(event) {
			// if the event was triggered by a mousedown and not the primary
			// button, or if the component is disabled, ignore it.
			if (this.props.disabled || event.type === 'mousedown' && event.button !== 0) {
				return;
			}

			if (this.state.isOpen) {
				// prevent default event handlers
				event.stopPropagation();
				event.preventDefault();
				// close the menu
				this.closeMenu();
			} else {
				// If the menu isn't open, let the event bubble to the main handleMouseDown
				this.setState({
					isOpen: true
				});
			}
		}
	}, {
		key: 'handleMouseDownOnMenu',
		value: function handleMouseDownOnMenu(event) {
			// if the event was triggered by a mousedown and not the primary
			// button, or if the component is disabled, ignore it.
			if (this.props.disabled || event.type === 'mousedown' && event.button !== 0) {
				return;
			}

			event.stopPropagation();
			event.preventDefault();

			this._openAfterFocus = true;
			this.focus();
		}
	}, {
		key: 'closeMenu',
		value: function closeMenu() {
			if (this.props.onCloseResetsInput) {
				this.setState({
					inputValue: this.handleInputValueChange(''),
					isOpen: false,
					isPseudoFocused: this.state.isFocused && !this.props.multi
				});
			} else {
				this.setState({
					isOpen: false,
					isPseudoFocused: this.state.isFocused && !this.props.multi
				});
			}
			this.hasScrolledToOption = false;
		}
	}, {
		key: 'handleInputFocus',
		value: function handleInputFocus(event) {
			if (this.props.disabled) return;

			var toOpen = this.state.isOpen || this._openAfterFocus || this.props.openOnFocus;
			toOpen = this._focusAfterClear ? false : toOpen; //if focus happens after clear values, don't open dropdown yet.

			if (this.props.onFocus) {
				this.props.onFocus(event);
			}

			this.setState({
				isFocused: true,
				isOpen: !!toOpen
			});

			this._focusAfterClear = false;
			this._openAfterFocus = false;
		}
	}, {
		key: 'handleInputBlur',
		value: function handleInputBlur(event) {
			// The check for menu.contains(activeElement) is necessary to prevent IE11's scrollbar from closing the menu in certain contexts.
			if (this.menu && (this.menu === document.activeElement || this.menu.contains(document.activeElement))) {
				this.focus();
				return;
			}

			if (this.props.onBlur) {
				this.props.onBlur(event);
			}
			var onBlurredState = {
				isFocused: false,
				isOpen: false,
				isPseudoFocused: false
			};
			if (this.props.onBlurResetsInput) {
				onBlurredState.inputValue = this.handleInputValueChange('');
			}
			this.setState(onBlurredState);
		}
	}, {
		key: 'handleInputChange',
		value: function handleInputChange(event) {
			var newInputValue = event.target.value;

			if (this.state.inputValue !== event.target.value) {
				newInputValue = this.handleInputValueChange(newInputValue);
			}

			this.setState({
				inputValue: newInputValue,
				isOpen: true,
				isPseudoFocused: false
			});
		}
	}, {
		key: 'setInputValue',
		value: function setInputValue(newValue) {
			if (this.props.onInputChange) {
				var nextState = this.props.onInputChange(newValue);
				if (nextState != null && (typeof nextState === 'undefined' ? 'undefined' : _typeof(nextState)) !== 'object') {
					newValue = '' + nextState;
				}
			}
			this.setState({
				inputValue: newValue
			});
		}
	}, {
		key: 'handleInputValueChange',
		value: function handleInputValueChange(newValue) {
			if (this.props.onInputChange) {
				var nextState = this.props.onInputChange(newValue);
				// Note: != used deliberately here to catch undefined and null
				if (nextState != null && (typeof nextState === 'undefined' ? 'undefined' : _typeof(nextState)) !== 'object') {
					newValue = '' + nextState;
				}
			}
			return newValue;
		}
	}, {
		key: 'handleKeyDown',
		value: function handleKeyDown(event) {
			if (this.props.disabled) return;

			if (typeof this.props.onInputKeyDown === 'function') {
				this.props.onInputKeyDown(event);
				if (event.defaultPrevented) {
					return;
				}
			}

			switch (event.keyCode) {
				case 8:
					// backspace
					if (!this.state.inputValue && this.props.backspaceRemoves) {
						event.preventDefault();
						this.popValue();
					}
					break;
				case 9:
					// tab
					if (event.shiftKey || !this.state.isOpen || !this.props.tabSelectsValue) {
						break;
					}
					event.preventDefault();
					this.selectFocusedOption();
					break;
				case 13:
					// enter
					event.preventDefault();
					event.stopPropagation();
					if (this.state.isOpen) {
						this.selectFocusedOption();
					} else {
						this.focusNextOption();
					}
					break;
				case 27:
					// escape
					event.preventDefault();
					if (this.state.isOpen) {
						this.closeMenu();
						event.stopPropagation();
					} else if (this.props.clearable && this.props.escapeClearsValue) {
						this.clearValue(event);
						event.stopPropagation();
					}
					break;
				case 32:
					// space
					if (this.props.searchable) {
						break;
					}
					event.preventDefault();
					if (!this.state.isOpen) {
						this.focusNextOption();
						break;
					}
					event.stopPropagation();
					this.selectFocusedOption();
					break;
				case 38:
					// up
					event.preventDefault();
					this.focusPreviousOption();
					break;
				case 40:
					// down
					event.preventDefault();
					this.focusNextOption();
					break;
				case 33:
					// page up
					event.preventDefault();
					this.focusPageUpOption();
					break;
				case 34:
					// page down
					event.preventDefault();
					this.focusPageDownOption();
					break;
				case 35:
					// end key
					if (event.shiftKey) {
						break;
					}
					event.preventDefault();
					this.focusEndOption();
					break;
				case 36:
					// home key
					if (event.shiftKey) {
						break;
					}
					event.preventDefault();
					this.focusStartOption();
					break;
				case 46:
					// delete
					if (!this.state.inputValue && this.props.deleteRemoves) {
						event.preventDefault();
						this.popValue();
					}
					break;
			}
		}
	}, {
		key: 'handleValueClick',
		value: function handleValueClick(option, event) {
			if (!this.props.onValueClick) return;
			this.props.onValueClick(option, event);
		}
	}, {
		key: 'handleMenuScroll',
		value: function handleMenuScroll(event) {
			if (!this.props.onMenuScrollToBottom) return;
			var target = event.target;

			if (target.scrollHeight > target.offsetHeight && target.scrollHeight - target.offsetHeight - target.scrollTop <= 0) {
				this.props.onMenuScrollToBottom();
			}
		}
	}, {
		key: 'getOptionLabel',
		value: function getOptionLabel(op) {
			return op[this.props.labelKey];
		}

		/**
   * Turns a value into an array from the given options
   * @param {String|Number|Array} value		- the value of the select input
   * @param {Object}		nextProps	- optionally specify the nextProps so the returned array uses the latest configuration
   * @returns	{Array}	the value of the select represented in an array
   */

	}, {
		key: 'getValueArray',
		value: function getValueArray(value) {
			var nextProps = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : undefined;

			/** support optionally passing in the `nextProps` so `componentWillReceiveProps` updates will function as expected */
			var props = (typeof nextProps === 'undefined' ? 'undefined' : _typeof(nextProps)) === 'object' ? nextProps : this.props;
			if (props.multi) {
				if (typeof value === 'string') {
					value = value.split(props.delimiter);
				}
				if (!Array.isArray(value)) {
					if (value === null || value === undefined) return [];
					value = [value];
				}
				return value.map(function (value) {
					return expandValue(value, props);
				}).filter(function (i) {
					return i;
				});
			}
			var expandedValue = expandValue(value, props);
			return expandedValue ? [expandedValue] : [];
		}
	}, {
		key: 'setValue',
		value: function setValue(value) {
			var _this2 = this;

			if (this.props.autoBlur) {
				this.blurInput();
			}
			if (this.props.required) {
				var required = handleRequired(value, this.props.multi);
				this.setState({ required: required });
			}
			if (this.props.simpleValue && value) {
				value = this.props.multi ? value.map(function (i) {
					return i[_this2.props.valueKey];
				}).join(this.props.delimiter) : value[this.props.valueKey];
			}
			if (this.props.onChange) {
				this.props.onChange(value);
			}
		}
	}, {
		key: 'selectValue',
		value: function selectValue(value) {
			var _this3 = this;

			// NOTE: we actually add/set the value in a callback to make sure the
			// input value is empty to avoid styling issues in Chrome
			if (this.props.closeOnSelect) {
				this.hasScrolledToOption = false;
			}
			var updatedValue = this.props.onSelectResetsInput ? '' : this.state.inputValue;
			if (this.props.multi) {
				this.setState({
					focusedIndex: null,
					inputValue: this.handleInputValueChange(updatedValue),
					isOpen: !this.props.closeOnSelect
				}, function () {
					var valueArray = _this3.getValueArray(_this3.props.value);
					if (valueArray.some(function (i) {
						return i[_this3.props.valueKey] === value[_this3.props.valueKey];
					})) {
						_this3.removeValue(value);
					} else {
						_this3.addValue(value);
					}
				});
			} else {
				this.setState({
					inputValue: this.handleInputValueChange(updatedValue),
					isOpen: !this.props.closeOnSelect,
					isPseudoFocused: this.state.isFocused
				}, function () {
					_this3.setValue(value);
				});
			}
		}
	}, {
		key: 'addValue',
		value: function addValue(value) {
			var valueArray = this.getValueArray(this.props.value);
			var visibleOptions = this._visibleOptions.filter(function (val) {
				return !val.disabled;
			});
			var lastValueIndex = visibleOptions.indexOf(value);
			this.setValue(valueArray.concat(value));
			if (!this.props.closeOnSelect) {
				return;
			}
			if (visibleOptions.length - 1 === lastValueIndex) {
				// the last option was selected; focus the second-last one
				this.focusOption(visibleOptions[lastValueIndex - 1]);
			} else if (visibleOptions.length > lastValueIndex) {
				// focus the option below the selected one
				this.focusOption(visibleOptions[lastValueIndex + 1]);
			}
		}
	}, {
		key: 'popValue',
		value: function popValue() {
			var valueArray = this.getValueArray(this.props.value);
			if (!valueArray.length) return;
			if (valueArray[valueArray.length - 1].clearableValue === false) return;
			this.setValue(this.props.multi ? valueArray.slice(0, valueArray.length - 1) : null);
		}
	}, {
		key: 'removeValue',
		value: function removeValue(value) {
			var _this4 = this;

			var valueArray = this.getValueArray(this.props.value);
			this.setValue(valueArray.filter(function (i) {
				return i[_this4.props.valueKey] !== value[_this4.props.valueKey];
			}));
			this.focus();
		}
	}, {
		key: 'clearValue',
		value: function clearValue(event) {
			// if the event was triggered by a mousedown and not the primary
			// button, ignore it.
			if (event && event.type === 'mousedown' && event.button !== 0) {
				return;
			}

			event.preventDefault();

			this.setValue(this.getResetValue());
			this.setState({
				inputValue: this.handleInputValueChange(''),
				isOpen: false
			}, this.focus);

			this._focusAfterClear = true;
		}
	}, {
		key: 'getResetValue',
		value: function getResetValue() {
			if (this.props.resetValue !== undefined) {
				return this.props.resetValue;
			} else if (this.props.multi) {
				return [];
			} else {
				return null;
			}
		}
	}, {
		key: 'focusOption',
		value: function focusOption(option) {
			this.setState({
				focusedOption: option
			});
		}
	}, {
		key: 'focusNextOption',
		value: function focusNextOption() {
			this.focusAdjacentOption('next');
		}
	}, {
		key: 'focusPreviousOption',
		value: function focusPreviousOption() {
			this.focusAdjacentOption('previous');
		}
	}, {
		key: 'focusPageUpOption',
		value: function focusPageUpOption() {
			this.focusAdjacentOption('page_up');
		}
	}, {
		key: 'focusPageDownOption',
		value: function focusPageDownOption() {
			this.focusAdjacentOption('page_down');
		}
	}, {
		key: 'focusStartOption',
		value: function focusStartOption() {
			this.focusAdjacentOption('start');
		}
	}, {
		key: 'focusEndOption',
		value: function focusEndOption() {
			this.focusAdjacentOption('end');
		}
	}, {
		key: 'focusAdjacentOption',
		value: function focusAdjacentOption(dir) {
			var options = this._visibleOptions.map(function (option, index) {
				return { option: option, index: index };
			}).filter(function (option) {
				return !option.option.disabled;
			});
			this._scrollToFocusedOptionOnUpdate = true;
			if (!this.state.isOpen) {
				var newState = {
					focusedOption: this._focusedOption || (options.length ? options[dir === 'next' ? 0 : options.length - 1].option : null),
					isOpen: true
				};
				if (this.props.onSelectResetsInput) {
					newState.inputValue = '';
				}
				this.setState(newState);
				return;
			}
			if (!options.length) return;
			var focusedIndex = -1;
			for (var i = 0; i < options.length; i++) {
				if (this._focusedOption === options[i].option) {
					focusedIndex = i;
					break;
				}
			}
			if (dir === 'next' && focusedIndex !== -1) {
				focusedIndex = (focusedIndex + 1) % options.length;
			} else if (dir === 'previous') {
				if (focusedIndex > 0) {
					focusedIndex = focusedIndex - 1;
				} else {
					focusedIndex = options.length - 1;
				}
			} else if (dir === 'start') {
				focusedIndex = 0;
			} else if (dir === 'end') {
				focusedIndex = options.length - 1;
			} else if (dir === 'page_up') {
				var potentialIndex = focusedIndex - this.props.pageSize;
				if (potentialIndex < 0) {
					focusedIndex = 0;
				} else {
					focusedIndex = potentialIndex;
				}
			} else if (dir === 'page_down') {
				var _potentialIndex = focusedIndex + this.props.pageSize;
				if (_potentialIndex > options.length - 1) {
					focusedIndex = options.length - 1;
				} else {
					focusedIndex = _potentialIndex;
				}
			}

			if (focusedIndex === -1) {
				focusedIndex = 0;
			}

			this.setState({
				focusedIndex: options[focusedIndex].index,
				focusedOption: options[focusedIndex].option
			});
		}
	}, {
		key: 'getFocusedOption',
		value: function getFocusedOption() {
			return this._focusedOption;
		}
	}, {
		key: 'selectFocusedOption',
		value: function selectFocusedOption() {
			if (this._focusedOption) {
				return this.selectValue(this._focusedOption);
			}
		}
	}, {
		key: 'renderLoading',
		value: function renderLoading() {
			if (!this.props.isLoading) return;
			return React__default.createElement(
				'span',
				{ className: 'Select-loading-zone', 'aria-hidden': 'true' },
				React__default.createElement('span', { className: 'Select-loading' })
			);
		}
	}, {
		key: 'renderValue',
		value: function renderValue(valueArray, isOpen) {
			var _this5 = this;

			var renderLabel = this.props.valueRenderer || this.getOptionLabel;
			var ValueComponent = this.props.valueComponent;
			if (!valueArray.length) {
				var showPlaceholder = shouldShowPlaceholder(this.state, this.props, isOpen);
				return showPlaceholder ? React__default.createElement(
					'div',
					{ className: 'Select-placeholder' },
					this.props.placeholder
				) : null;
			}
			var onClick = this.props.onValueClick ? this.handleValueClick : null;
			if (this.props.multi) {
				return valueArray.map(function (value, i) {
					return React__default.createElement(
						ValueComponent,
						{
							disabled: _this5.props.disabled || value.clearableValue === false,
							id: _this5._instancePrefix + '-value-' + i,
							instancePrefix: _this5._instancePrefix,
							key: 'value-' + i + '-' + value[_this5.props.valueKey],
							onClick: onClick,
							onRemove: _this5.removeValue,
							placeholder: _this5.props.placeholder,
							value: value,
							values: valueArray
						},
						renderLabel(value, i),
						React__default.createElement(
							'span',
							{ className: 'Select-aria-only' },
							'\xA0'
						)
					);
				});
			} else if (shouldShowValue(this.state, this.props)) {
				if (isOpen) onClick = null;
				return React__default.createElement(
					ValueComponent,
					{
						disabled: this.props.disabled,
						id: this._instancePrefix + '-value-item',
						instancePrefix: this._instancePrefix,
						onClick: onClick,
						placeholder: this.props.placeholder,
						value: valueArray[0]
					},
					renderLabel(valueArray[0])
				);
			}
		}
	}, {
		key: 'renderInput',
		value: function renderInput(valueArray, focusedOptionIndex) {
			var _classNames,
			    _this6 = this;

			var className = cx('Select-input', this.props.inputProps.className);
			var isOpen = this.state.isOpen;

			var ariaOwns = cx((_classNames = {}, defineProperty(_classNames, this._instancePrefix + '-list', isOpen), defineProperty(_classNames, this._instancePrefix + '-backspace-remove-message', this.props.multi && !this.props.disabled && this.state.isFocused && !this.state.inputValue), _classNames));

			var value = this.state.inputValue;
			if (value && !this.props.onSelectResetsInput && !this.state.isFocused) {
				// it hides input value when it is not focused and was not reset on select
				value = '';
			}

			var inputProps = _extends({}, this.props.inputProps, {
				'aria-activedescendant': isOpen ? this._instancePrefix + '-option-' + focusedOptionIndex : this._instancePrefix + '-value',
				'aria-describedby': this.props['aria-describedby'],
				'aria-expanded': '' + isOpen,
				'aria-haspopup': '' + isOpen,
				'aria-label': this.props['aria-label'],
				'aria-labelledby': this.props['aria-labelledby'],
				'aria-owns': ariaOwns,
				onBlur: this.handleInputBlur,
				onChange: this.handleInputChange,
				onFocus: this.handleInputFocus,
				ref: function ref(_ref) {
					return _this6.input = _ref;
				},
				role: 'combobox',
				required: this.state.required,
				tabIndex: this.props.tabIndex,
				value: value
			});

			if (this.props.inputRenderer) {
				return this.props.inputRenderer(inputProps);
			}

			if (this.props.disabled || !this.props.searchable) {
				var divProps = objectWithoutProperties(this.props.inputProps, []);


				var _ariaOwns = cx(defineProperty({}, this._instancePrefix + '-list', isOpen));
				return React__default.createElement('div', _extends({}, divProps, {
					'aria-expanded': isOpen,
					'aria-owns': _ariaOwns,
					'aria-activedescendant': isOpen ? this._instancePrefix + '-option-' + focusedOptionIndex : this._instancePrefix + '-value',
					'aria-disabled': '' + this.props.disabled,
					'aria-label': this.props['aria-label'],
					'aria-labelledby': this.props['aria-labelledby'],
					className: className,
					onBlur: this.handleInputBlur,
					onFocus: this.handleInputFocus,
					ref: function ref(_ref2) {
						return _this6.input = _ref2;
					},
					role: 'combobox',
					style: { border: 0, width: 1, display: 'inline-block' },
					tabIndex: this.props.tabIndex || 0
				}));
			}

			if (this.props.autosize) {
				return React__default.createElement(AutosizeInput, _extends({ id: this.props.id }, inputProps, { className: className, minWidth: '5' }));
			}
			return React__default.createElement(
				'div',
				{ className: className, key: 'input-wrap', style: { display: 'inline-block' } },
				React__default.createElement('input', _extends({ id: this.props.id }, inputProps))
			);
		}
	}, {
		key: 'renderClear',
		value: function renderClear() {
			var valueArray = this.getValueArray(this.props.value);
			if (!this.props.clearable || !valueArray.length || this.props.disabled || this.props.isLoading) return;
			var ariaLabel = this.props.multi ? this.props.clearAllText : this.props.clearValueText;
			var clear = this.props.clearRenderer();

			return React__default.createElement(
				'span',
				{
					'aria-label': ariaLabel,
					className: 'Select-clear-zone',
					onMouseDown: this.clearValue,
					onTouchEnd: this.handleTouchEndClearValue,
					onTouchMove: this.handleTouchMove,
					onTouchStart: this.handleTouchStart,
					title: ariaLabel
				},
				clear
			);
		}
	}, {
		key: 'renderArrow',
		value: function renderArrow() {
			if (!this.props.arrowRenderer) return;

			var onMouseDown = this.handleMouseDownOnArrow;
			var isOpen = this.state.isOpen;
			var arrow = this.props.arrowRenderer({ onMouseDown: onMouseDown, isOpen: isOpen });

			if (!arrow) {
				return null;
			}

			return React__default.createElement(
				'span',
				{
					className: 'Select-arrow-zone',
					onMouseDown: onMouseDown
				},
				arrow
			);
		}
	}, {
		key: 'filterOptions',
		value: function filterOptions$$1(excludeOptions) {
			var filterValue = this.state.inputValue;
			var options = this.props.options || [];
			if (this.props.filterOptions) {
				// Maintain backwards compatibility with boolean attribute
				var filterOptions$$1 = typeof this.props.filterOptions === 'function' ? this.props.filterOptions : filterOptions;

				return filterOptions$$1(options, filterValue, excludeOptions, {
					filterOption: this.props.filterOption,
					ignoreAccents: this.props.ignoreAccents,
					ignoreCase: this.props.ignoreCase,
					labelKey: this.props.labelKey,
					matchPos: this.props.matchPos,
					matchProp: this.props.matchProp,
					trimFilter: this.props.trimFilter,
					valueKey: this.props.valueKey
				});
			} else {
				return options;
			}
		}
	}, {
		key: 'onOptionRef',
		value: function onOptionRef(ref, isFocused) {
			if (isFocused) {
				this.focused = ref;
			}
		}
	}, {
		key: 'renderMenu',
		value: function renderMenu(options, valueArray, focusedOption) {
			if (options && options.length) {
				return this.props.menuRenderer({
					focusedOption: focusedOption,
					focusOption: this.focusOption,
					inputValue: this.state.inputValue,
					instancePrefix: this._instancePrefix,
					labelKey: this.props.labelKey,
					onFocus: this.focusOption,
					onOptionRef: this.onOptionRef,
					onSelect: this.selectValue,
					optionClassName: this.props.optionClassName,
					optionComponent: this.props.optionComponent,
					optionRenderer: this.props.optionRenderer || this.getOptionLabel,
					options: options,
					removeValue: this.removeValue,
					selectValue: this.selectValue,
					valueArray: valueArray,
					valueKey: this.props.valueKey
				});
			} else if (this.props.noResultsText) {
				return React__default.createElement(
					'div',
					{ className: 'Select-noresults' },
					this.props.noResultsText
				);
			} else {
				return null;
			}
		}
	}, {
		key: 'renderHiddenField',
		value: function renderHiddenField(valueArray) {
			var _this7 = this;

			if (!this.props.name) return;
			if (this.props.joinValues) {
				var value = valueArray.map(function (i) {
					return stringifyValue(i[_this7.props.valueKey]);
				}).join(this.props.delimiter);
				return React__default.createElement('input', {
					disabled: this.props.disabled,
					name: this.props.name,
					ref: function ref(_ref3) {
						return _this7.value = _ref3;
					},
					type: 'hidden',
					value: value
				});
			}
			return valueArray.map(function (item, index) {
				return React__default.createElement('input', {
					disabled: _this7.props.disabled,
					key: 'hidden.' + index,
					name: _this7.props.name,
					ref: 'value' + index,
					type: 'hidden',
					value: stringifyValue(item[_this7.props.valueKey])
				});
			});
		}
	}, {
		key: 'getFocusableOptionIndex',
		value: function getFocusableOptionIndex(selectedOption) {
			var options = this._visibleOptions;
			if (!options.length) return null;

			var valueKey = this.props.valueKey;
			var focusedOption = this.state.focusedOption || selectedOption;
			if (focusedOption && !focusedOption.disabled) {
				var focusedOptionIndex = -1;
				options.some(function (option, index) {
					var isOptionEqual = option[valueKey] === focusedOption[valueKey];
					if (isOptionEqual) {
						focusedOptionIndex = index;
					}
					return isOptionEqual;
				});
				if (focusedOptionIndex !== -1) {
					return focusedOptionIndex;
				}
			}

			for (var i = 0; i < options.length; i++) {
				if (!options[i].disabled) return i;
			}
			return null;
		}
	}, {
		key: 'renderOuter',
		value: function renderOuter(options, valueArray, focusedOption) {
			var _this8 = this;

			var menu = this.renderMenu(options, valueArray, focusedOption);
			if (!menu) {
				return null;
			}

			return React__default.createElement(
				'div',
				{ ref: function ref(_ref5) {
						return _this8.menuContainer = _ref5;
					}, className: 'Select-menu-outer', style: this.props.menuContainerStyle },
				React__default.createElement(
					'div',
					{
						className: 'Select-menu',
						id: this._instancePrefix + '-list',
						onMouseDown: this.handleMouseDownOnMenu,
						onScroll: this.handleMenuScroll,
						ref: function ref(_ref4) {
							return _this8.menu = _ref4;
						},
						role: 'listbox',
						style: this.props.menuStyle,
						tabIndex: -1
					},
					menu
				)
			);
		}
	}, {
		key: 'render',
		value: function render() {
			var _this9 = this;

			var valueArray = this.getValueArray(this.props.value);
			var options = this._visibleOptions = this.filterOptions(this.props.multi && this.props.removeSelected ? valueArray : null);
			var isOpen = this.state.isOpen;
			if (this.props.multi && !options.length && valueArray.length && !this.state.inputValue) isOpen = false;
			var focusedOptionIndex = this.getFocusableOptionIndex(valueArray[0]);

			var focusedOption = null;
			if (focusedOptionIndex !== null) {
				focusedOption = this._focusedOption = options[focusedOptionIndex];
			} else {
				focusedOption = this._focusedOption = null;
			}
			var className = cx('Select', this.props.className, {
				'has-value': valueArray.length,
				'is-clearable': this.props.clearable,
				'is-disabled': this.props.disabled,
				'is-focused': this.state.isFocused,
				'is-loading': this.props.isLoading,
				'is-open': isOpen,
				'is-pseudo-focused': this.state.isPseudoFocused,
				'is-searchable': this.props.searchable,
				'Select--multi': this.props.multi,
				'Select--rtl': this.props.rtl,
				'Select--single': !this.props.multi
			});

			var removeMessage = null;
			if (this.props.multi && !this.props.disabled && valueArray.length && !this.state.inputValue && this.state.isFocused && this.props.backspaceRemoves) {
				removeMessage = React__default.createElement(
					'span',
					{ id: this._instancePrefix + '-backspace-remove-message', className: 'Select-aria-only', 'aria-live': 'assertive' },
					this.props.backspaceToRemoveMessage.replace('{label}', valueArray[valueArray.length - 1][this.props.labelKey])
				);
			}

			return React__default.createElement(
				'div',
				{ ref: function ref(_ref7) {
						return _this9.wrapper = _ref7;
					},
					className: className,
					style: this.props.wrapperStyle },
				this.renderHiddenField(valueArray),
				React__default.createElement(
					'div',
					{ ref: function ref(_ref6) {
							return _this9.control = _ref6;
						},
						className: 'Select-control',
						onKeyDown: this.handleKeyDown,
						onMouseDown: this.handleMouseDown,
						onTouchEnd: this.handleTouchEnd,
						onTouchMove: this.handleTouchMove,
						onTouchStart: this.handleTouchStart,
						style: this.props.style
					},
					React__default.createElement(
						'div',
						{ className: 'Select-multi-value-wrapper', id: this._instancePrefix + '-value' },
						this.renderValue(valueArray, isOpen),
						this.renderInput(valueArray, focusedOptionIndex)
					),
					removeMessage,
					this.renderLoading(),
					this.renderClear(),
					this.renderArrow()
				),
				isOpen ? this.renderOuter(options, valueArray, focusedOption) : null
			);
		}
	}]);
	return Select;
}(React__default.Component);

Select$1.propTypes = {
	'aria-describedby': propTypes.string, // html id(s) of element(s) that should be used to describe this input (for assistive tech)
	'aria-label': propTypes.string, // aria label (for assistive tech)
	'aria-labelledby': propTypes.string, // html id of an element that should be used as the label (for assistive tech)
	arrowRenderer: propTypes.func, // create the drop-down caret element
	autoBlur: propTypes.bool, // automatically blur the component when an option is selected
	autoFocus: propTypes.bool, // autofocus the component on mount
	autofocus: propTypes.bool, // deprecated; use autoFocus instead
	autosize: propTypes.bool, // whether to enable autosizing or not
	backspaceRemoves: propTypes.bool, // whether backspace removes an item if there is no text input
	backspaceToRemoveMessage: propTypes.string, // message to use for screenreaders to press backspace to remove the current item - {label} is replaced with the item label
	className: propTypes.string, // className for the outer element
	clearAllText: stringOrNode, // title for the "clear" control when multi: true
	clearRenderer: propTypes.func, // create clearable x element
	clearValueText: stringOrNode, // title for the "clear" control
	clearable: propTypes.bool, // should it be possible to reset value
	closeOnSelect: propTypes.bool, // whether to close the menu when a value is selected
	deleteRemoves: propTypes.bool, // whether delete removes an item if there is no text input
	delimiter: propTypes.string, // delimiter to use to join multiple values for the hidden field value
	disabled: propTypes.bool, // whether the Select is disabled or not
	escapeClearsValue: propTypes.bool, // whether escape clears the value when the menu is closed
	filterOption: propTypes.func, // method to filter a single option (option, filterString)
	filterOptions: propTypes.any, // boolean to enable default filtering or function to filter the options array ([options], filterString, [values])
	id: propTypes.string, // html id to set on the input element for accessibility or tests
	ignoreAccents: propTypes.bool, // whether to strip diacritics when filtering
	ignoreCase: propTypes.bool, // whether to perform case-insensitive filtering
	inputProps: propTypes.object, // custom attributes for the Input
	inputRenderer: propTypes.func, // returns a custom input component
	instanceId: propTypes.string, // set the components instanceId
	isLoading: propTypes.bool, // whether the Select is loading externally or not (such as options being loaded)
	joinValues: propTypes.bool, // joins multiple values into a single form field with the delimiter (legacy mode)
	labelKey: propTypes.string, // path of the label value in option objects
	matchPos: propTypes.string, // (any|start) match the start or entire string when filtering
	matchProp: propTypes.string, // (any|label|value) which option property to filter on
	menuBuffer: propTypes.number, // optional buffer (in px) between the bottom of the viewport and the bottom of the menu
	menuContainerStyle: propTypes.object, // optional style to apply to the menu container
	menuRenderer: propTypes.func, // renders a custom menu with options
	menuStyle: propTypes.object, // optional style to apply to the menu
	multi: propTypes.bool, // multi-value input
	name: propTypes.string, // generates a hidden <input /> tag with this field name for html forms
	noResultsText: stringOrNode, // placeholder displayed when there are no matching search results
	onBlur: propTypes.func, // onBlur handler: function (event) {}
	onBlurResetsInput: propTypes.bool, // whether input is cleared on blur
	onChange: propTypes.func, // onChange handler: function (newValue) {}
	onClose: propTypes.func, // fires when the menu is closed
	onCloseResetsInput: propTypes.bool, // whether input is cleared when menu is closed through the arrow
	onFocus: propTypes.func, // onFocus handler: function (event) {}
	onInputChange: propTypes.func, // onInputChange handler: function (inputValue) {}
	onInputKeyDown: propTypes.func, // input keyDown handler: function (event) {}
	onMenuScrollToBottom: propTypes.func, // fires when the menu is scrolled to the bottom; can be used to paginate options
	onOpen: propTypes.func, // fires when the menu is opened
	onSelectResetsInput: propTypes.bool, // whether input is cleared on select (works only for multiselect)
	onValueClick: propTypes.func, // onClick handler for value labels: function (value, event) {}
	openOnClick: propTypes.bool, // boolean to control opening the menu when the control is clicked
	openOnFocus: propTypes.bool, // always open options menu on focus
	optionClassName: propTypes.string, // additional class(es) to apply to the <Option /> elements
	optionComponent: propTypes.func, // option component to render in dropdown
	optionRenderer: propTypes.func, // optionRenderer: function (option) {}
	options: propTypes.array, // array of options
	pageSize: propTypes.number, // number of entries to page when using page up/down keys
	placeholder: stringOrNode, // field placeholder, displayed when there's no value
	removeSelected: propTypes.bool, // whether the selected option is removed from the dropdown on multi selects
	required: propTypes.bool, // applies HTML5 required attribute when needed
	resetValue: propTypes.any, // value to use when you clear the control
	rtl: propTypes.bool, // set to true in order to use react-select in right-to-left direction
	scrollMenuIntoView: propTypes.bool, // boolean to enable the viewport to shift so that the full menu fully visible when engaged
	searchable: propTypes.bool, // whether to enable searching feature or not
	simpleValue: propTypes.bool, // pass the value to onChange as a simple value (legacy pre 1.0 mode), defaults to false
	style: propTypes.object, // optional style to apply to the control
	tabIndex: stringOrNumber, // optional tab index of the control
	tabSelectsValue: propTypes.bool, // whether to treat tabbing out while focused to be value selection
	trimFilter: propTypes.bool, // whether to trim whitespace around filter value
	value: propTypes.any, // initial field value
	valueComponent: propTypes.func, // value component to render
	valueKey: propTypes.string, // path of the label value in option objects
	valueRenderer: propTypes.func, // valueRenderer: function (option) {}
	wrapperStyle: propTypes.object // optional style to apply to the component wrapper
};

Select$1.defaultProps = {
	arrowRenderer: arrowRenderer,
	autosize: true,
	backspaceRemoves: true,
	backspaceToRemoveMessage: 'Press backspace to remove {label}',
	clearable: true,
	clearAllText: 'Clear all',
	clearRenderer: clearRenderer,
	clearValueText: 'Clear value',
	closeOnSelect: true,
	deleteRemoves: true,
	delimiter: ',',
	disabled: false,
	escapeClearsValue: true,
	filterOptions: filterOptions,
	ignoreAccents: true,
	ignoreCase: true,
	inputProps: {},
	isLoading: false,
	joinValues: false,
	labelKey: 'label',
	matchPos: 'any',
	matchProp: 'any',
	menuBuffer: 0,
	menuRenderer: menuRenderer,
	multi: false,
	noResultsText: 'No results found',
	onBlurResetsInput: true,
	onCloseResetsInput: true,
	onSelectResetsInput: true,
	openOnClick: true,
	optionComponent: Option,
	pageSize: 5,
	placeholder: 'Select...',
	removeSelected: true,
	required: false,
	rtl: false,
	scrollMenuIntoView: true,
	searchable: true,
	simpleValue: false,
	tabSelectsValue: true,
	trimFilter: true,
	valueComponent: Value,
	valueKey: 'value'
};

var propTypes$1 = {
	autoload: propTypes.bool.isRequired, // automatically call the `loadOptions` prop on-mount; defaults to true
	cache: propTypes.any, // object to use to cache results; set to null/false to disable caching
	children: propTypes.func.isRequired, // Child function responsible for creating the inner Select component; (props: Object): PropTypes.element
	ignoreAccents: propTypes.bool, // strip diacritics when filtering; defaults to true
	ignoreCase: propTypes.bool, // perform case-insensitive filtering; defaults to true
	loadOptions: propTypes.func.isRequired, // callback to load options asynchronously; (inputValue: string, callback: Function): ?Promise
	loadingPlaceholder: propTypes.oneOfType([// replaces the placeholder while options are loading
	propTypes.string, propTypes.node]),
	multi: propTypes.bool, // multi-value input
	noResultsText: propTypes.oneOfType([// field noResultsText, displayed when no options come back from the server
	propTypes.string, propTypes.node]),
	onChange: propTypes.func, // onChange handler: function (newValue) {}
	onInputChange: propTypes.func, // optional for keeping track of what is being typed
	options: propTypes.array.isRequired, // array of options
	placeholder: propTypes.oneOfType([// field placeholder, displayed when there's no value (shared with Select)
	propTypes.string, propTypes.node]),
	searchPromptText: propTypes.oneOfType([// label to prompt for search input
	propTypes.string, propTypes.node]),
	value: propTypes.any // initial field value
};

var defaultCache = {};

var defaultChildren = function defaultChildren(props) {
	return React__default.createElement(Select$1, props);
};

var defaultProps = {
	autoload: true,
	cache: defaultCache,
	children: defaultChildren,
	ignoreAccents: true,
	ignoreCase: true,
	loadingPlaceholder: 'Loading...',
	options: [],
	searchPromptText: 'Type to search'
};

var Async = function (_Component) {
	inherits(Async, _Component);

	function Async(props, context) {
		classCallCheck(this, Async);

		var _this = possibleConstructorReturn(this, (Async.__proto__ || Object.getPrototypeOf(Async)).call(this, props, context));

		_this._cache = props.cache === defaultCache ? {} : props.cache;

		_this.state = {
			inputValue: '',
			isLoading: false,
			options: props.options
		};

		_this.onInputChange = _this.onInputChange.bind(_this);
		return _this;
	}

	createClass(Async, [{
		key: 'componentDidMount',
		value: function componentDidMount() {
			var autoload = this.props.autoload;


			if (autoload) {
				this.loadOptions('');
			}
		}
	}, {
		key: 'componentWillReceiveProps',
		value: function componentWillReceiveProps(nextProps) {
			if (nextProps.options !== this.props.options) {
				this.setState({
					options: nextProps.options
				});
			}
		}
	}, {
		key: 'componentWillUnmount',
		value: function componentWillUnmount() {
			this._callback = null;
		}
	}, {
		key: 'loadOptions',
		value: function loadOptions(inputValue) {
			var _this2 = this;

			var loadOptions = this.props.loadOptions;

			var cache = this._cache;

			if (cache && Object.prototype.hasOwnProperty.call(cache, inputValue)) {
				this._callback = null;

				this.setState({
					isLoading: false,
					options: cache[inputValue]
				});

				return;
			}

			var callback = function callback(error, data) {
				var options = data && data.options || [];

				if (cache) {
					cache[inputValue] = options;
				}

				if (callback === _this2._callback) {
					_this2._callback = null;

					_this2.setState({
						isLoading: false,
						options: options
					});
				}
			};

			// Ignore all but the most recent request
			this._callback = callback;

			var promise = loadOptions(inputValue, callback);
			if (promise) {
				promise.then(function (data) {
					return callback(null, data);
				}, function (error) {
					return callback(error);
				});
			}

			if (this._callback && !this.state.isLoading) {
				this.setState({
					isLoading: true
				});
			}
		}
	}, {
		key: 'onInputChange',
		value: function onInputChange(inputValue) {
			var _props = this.props,
			    ignoreAccents = _props.ignoreAccents,
			    ignoreCase = _props.ignoreCase,
			    onInputChange = _props.onInputChange;

			var newInputValue = inputValue;

			if (onInputChange) {
				var value = onInputChange(newInputValue);
				// Note: != used deliberately here to catch undefined and null
				if (value != null && (typeof value === 'undefined' ? 'undefined' : _typeof(value)) !== 'object') {
					newInputValue = '' + value;
				}
			}

			var transformedInputValue = newInputValue;

			if (ignoreAccents) {
				transformedInputValue = stripDiacritics(transformedInputValue);
			}

			if (ignoreCase) {
				transformedInputValue = transformedInputValue.toLowerCase();
			}

			this.setState({ inputValue: newInputValue });
			this.loadOptions(transformedInputValue);

			// Return new input value, but without applying toLowerCase() to avoid modifying the user's view case of the input while typing.
			return newInputValue;
		}
	}, {
		key: 'noResultsText',
		value: function noResultsText() {
			var _props2 = this.props,
			    loadingPlaceholder = _props2.loadingPlaceholder,
			    noResultsText = _props2.noResultsText,
			    searchPromptText = _props2.searchPromptText;
			var _state = this.state,
			    inputValue = _state.inputValue,
			    isLoading = _state.isLoading;


			if (isLoading) {
				return loadingPlaceholder;
			}
			if (inputValue && noResultsText) {
				return noResultsText;
			}
			return searchPromptText;
		}
	}, {
		key: 'focus',
		value: function focus() {
			this.select.focus();
		}
	}, {
		key: 'render',
		value: function render() {
			var _this3 = this;

			var _props3 = this.props,
			    children = _props3.children,
			    loadingPlaceholder = _props3.loadingPlaceholder,
			    placeholder = _props3.placeholder;
			var _state2 = this.state,
			    isLoading = _state2.isLoading,
			    options = _state2.options;


			var props = {
				noResultsText: this.noResultsText(),
				placeholder: isLoading ? loadingPlaceholder : placeholder,
				options: isLoading && loadingPlaceholder ? [] : options,
				ref: function ref(_ref) {
					return _this3.select = _ref;
				}
			};

			return children(_extends({}, this.props, props, {
				isLoading: isLoading,
				onInputChange: this.onInputChange
			}));
		}
	}]);
	return Async;
}(React.Component);

Async.propTypes = propTypes$1;
Async.defaultProps = defaultProps;

var CreatableSelect = function (_React$Component) {
	inherits(CreatableSelect, _React$Component);

	function CreatableSelect(props, context) {
		classCallCheck(this, CreatableSelect);

		var _this = possibleConstructorReturn(this, (CreatableSelect.__proto__ || Object.getPrototypeOf(CreatableSelect)).call(this, props, context));

		_this.filterOptions = _this.filterOptions.bind(_this);
		_this.menuRenderer = _this.menuRenderer.bind(_this);
		_this.onInputKeyDown = _this.onInputKeyDown.bind(_this);
		_this.onInputChange = _this.onInputChange.bind(_this);
		_this.onOptionSelect = _this.onOptionSelect.bind(_this);
		return _this;
	}

	createClass(CreatableSelect, [{
		key: 'createNewOption',
		value: function createNewOption() {
			var _props = this.props,
			    isValidNewOption = _props.isValidNewOption,
			    newOptionCreator = _props.newOptionCreator,
			    onNewOptionClick = _props.onNewOptionClick,
			    _props$options = _props.options,
			    options = _props$options === undefined ? [] : _props$options;


			if (isValidNewOption({ label: this.inputValue })) {
				var option = newOptionCreator({ label: this.inputValue, labelKey: this.labelKey, valueKey: this.valueKey });
				var _isOptionUnique = this.isOptionUnique({ option: option, options: options });

				// Don't add the same option twice.
				if (_isOptionUnique) {
					if (onNewOptionClick) {
						onNewOptionClick(option);
					} else {
						options.unshift(option);

						this.select.selectValue(option);
					}
				}
			}
		}
	}, {
		key: 'filterOptions',
		value: function filterOptions$$1() {
			var _props2 = this.props,
			    filterOptions$$1 = _props2.filterOptions,
			    isValidNewOption = _props2.isValidNewOption,
			    promptTextCreator = _props2.promptTextCreator,
			    showNewOptionAtTop = _props2.showNewOptionAtTop;

			// TRICKY Check currently selected options as well.
			// Don't display a create-prompt for a value that's selected.
			// This covers async edge-cases where a newly-created Option isn't yet in the async-loaded array.

			var excludeOptions = (arguments.length <= 2 ? undefined : arguments[2]) || [];

			var filteredOptions = filterOptions$$1.apply(undefined, arguments) || [];

			if (isValidNewOption({ label: this.inputValue })) {
				var _newOptionCreator = this.props.newOptionCreator;


				var option = _newOptionCreator({
					label: this.inputValue,
					labelKey: this.labelKey,
					valueKey: this.valueKey
				});

				// TRICKY Compare to all options (not just filtered options) in case option has already been selected).
				// For multi-selects, this would remove it from the filtered list.
				var _isOptionUnique2 = this.isOptionUnique({
					option: option,
					options: excludeOptions.concat(filteredOptions)
				});

				if (_isOptionUnique2) {
					var prompt = promptTextCreator(this.inputValue);

					this._createPlaceholderOption = _newOptionCreator({
						label: prompt,
						labelKey: this.labelKey,
						valueKey: this.valueKey
					});

					if (showNewOptionAtTop) {
						filteredOptions.unshift(this._createPlaceholderOption);
					} else {
						filteredOptions.push(this._createPlaceholderOption);
					}
				}
			}

			return filteredOptions;
		}
	}, {
		key: 'isOptionUnique',
		value: function isOptionUnique(_ref) {
			var option = _ref.option,
			    options = _ref.options;
			var isOptionUnique = this.props.isOptionUnique;


			options = options || this.props.options;

			return isOptionUnique({
				labelKey: this.labelKey,
				option: option,
				options: options,
				valueKey: this.valueKey
			});
		}
	}, {
		key: 'menuRenderer',
		value: function menuRenderer$$1(params) {
			var menuRenderer$$1 = this.props.menuRenderer;


			return menuRenderer$$1(_extends({}, params, {
				onSelect: this.onOptionSelect,
				selectValue: this.onOptionSelect
			}));
		}
	}, {
		key: 'onInputChange',
		value: function onInputChange(input) {
			var onInputChange = this.props.onInputChange;

			// This value may be needed in between Select mounts (when this.select is null)

			this.inputValue = input;

			if (onInputChange) {
				this.inputValue = onInputChange(input);
			}

			return this.inputValue;
		}
	}, {
		key: 'onInputKeyDown',
		value: function onInputKeyDown(event) {
			var _props3 = this.props,
			    shouldKeyDownEventCreateNewOption = _props3.shouldKeyDownEventCreateNewOption,
			    onInputKeyDown = _props3.onInputKeyDown;

			var focusedOption = this.select.getFocusedOption();

			if (focusedOption && focusedOption === this._createPlaceholderOption && shouldKeyDownEventCreateNewOption(event)) {
				this.createNewOption();

				// Prevent decorated Select from doing anything additional with this keyDown event
				event.preventDefault();
			} else if (onInputKeyDown) {
				onInputKeyDown(event);
			}
		}
	}, {
		key: 'onOptionSelect',
		value: function onOptionSelect(option) {
			if (option === this._createPlaceholderOption) {
				this.createNewOption();
			} else {
				this.select.selectValue(option);
			}
		}
	}, {
		key: 'focus',
		value: function focus() {
			this.select.focus();
		}
	}, {
		key: 'render',
		value: function render() {
			var _this2 = this;

			var _props4 = this.props,
			    refProp = _props4.ref,
			    restProps = objectWithoutProperties(_props4, ['ref']);
			var children = this.props.children;

			// We can't use destructuring default values to set the children,
			// because it won't apply work if `children` is null. A falsy check is
			// more reliable in real world use-cases.

			if (!children) {
				children = defaultChildren$2;
			}

			var props = _extends({}, restProps, {
				allowCreate: true,
				filterOptions: this.filterOptions,
				menuRenderer: this.menuRenderer,
				onInputChange: this.onInputChange,
				onInputKeyDown: this.onInputKeyDown,
				ref: function ref(_ref2) {
					_this2.select = _ref2;

					// These values may be needed in between Select mounts (when this.select is null)
					if (_ref2) {
						_this2.labelKey = _ref2.props.labelKey;
						_this2.valueKey = _ref2.props.valueKey;
					}
					if (refProp) {
						refProp(_ref2);
					}
				}
			});

			return children(props);
		}
	}]);
	return CreatableSelect;
}(React__default.Component);

var defaultChildren$2 = function defaultChildren(props) {
	return React__default.createElement(Select$1, props);
};

var isOptionUnique = function isOptionUnique(_ref3) {
	var option = _ref3.option,
	    options = _ref3.options,
	    labelKey = _ref3.labelKey,
	    valueKey = _ref3.valueKey;

	if (!options || !options.length) {
		return true;
	}

	return options.filter(function (existingOption) {
		return existingOption[labelKey] === option[labelKey] || existingOption[valueKey] === option[valueKey];
	}).length === 0;
};

var isValidNewOption = function isValidNewOption(_ref4) {
	var label = _ref4.label;
	return !!label;
};

var newOptionCreator = function newOptionCreator(_ref5) {
	var label = _ref5.label,
	    labelKey = _ref5.labelKey,
	    valueKey = _ref5.valueKey;

	var option = {};
	option[valueKey] = label;
	option[labelKey] = label;
	option.className = 'Select-create-option-placeholder';

	return option;
};

var promptTextCreator = function promptTextCreator(label) {
	return 'Create option "' + label + '"';
};

var shouldKeyDownEventCreateNewOption = function shouldKeyDownEventCreateNewOption(_ref6) {
	var keyCode = _ref6.keyCode;

	switch (keyCode) {
		case 9: // TAB
		case 13: // ENTER
		case 188:
			// COMMA
			return true;
		default:
			return false;
	}
};

// Default prop methods
CreatableSelect.isOptionUnique = isOptionUnique;
CreatableSelect.isValidNewOption = isValidNewOption;
CreatableSelect.newOptionCreator = newOptionCreator;
CreatableSelect.promptTextCreator = promptTextCreator;
CreatableSelect.shouldKeyDownEventCreateNewOption = shouldKeyDownEventCreateNewOption;

CreatableSelect.defaultProps = {
	filterOptions: filterOptions,
	isOptionUnique: isOptionUnique,
	isValidNewOption: isValidNewOption,
	menuRenderer: menuRenderer,
	newOptionCreator: newOptionCreator,
	promptTextCreator: promptTextCreator,
	shouldKeyDownEventCreateNewOption: shouldKeyDownEventCreateNewOption,
	showNewOptionAtTop: true
};

CreatableSelect.propTypes = {
	// Child function responsible for creating the inner Select component
	// This component can be used to compose HOCs (eg Creatable and Async)
	// (props: Object): PropTypes.element
	children: propTypes.func,

	// See Select.propTypes.filterOptions
	filterOptions: propTypes.any,

	// Searches for any matching option within the set of options.
	// This function prevents duplicate options from being created.
	// ({ option: Object, options: Array, labelKey: string, valueKey: string }): boolean
	isOptionUnique: propTypes.func,

	// Determines if the current input text represents a valid option.
	// ({ label: string }): boolean
	isValidNewOption: propTypes.func,

	// See Select.propTypes.menuRenderer
	menuRenderer: propTypes.any,

	// Factory to create new option.
	// ({ label: string, labelKey: string, valueKey: string }): Object
	newOptionCreator: propTypes.func,

	// input change handler: function (inputValue) {}
	onInputChange: propTypes.func,

	// input keyDown handler: function (event) {}
	onInputKeyDown: propTypes.func,

	// new option click handler: function (option) {}
	onNewOptionClick: propTypes.func,

	// See Select.propTypes.options
	options: propTypes.array,

	// Creates prompt/placeholder option text.
	// (filterText: string): string
	promptTextCreator: propTypes.func,

	ref: propTypes.func,

	// Decides if a keyDown event (eg its `keyCode`) should result in the creation of a new option.
	shouldKeyDownEventCreateNewOption: propTypes.func,

	// Where to show prompt/placeholder option text.
	// true: new option prompt at top of list (default)
	// false: new option prompt at bottom of list
	showNewOptionAtTop: propTypes.bool
};

var AsyncCreatableSelect = function (_React$Component) {
	inherits(AsyncCreatableSelect, _React$Component);

	function AsyncCreatableSelect() {
		classCallCheck(this, AsyncCreatableSelect);
		return possibleConstructorReturn(this, (AsyncCreatableSelect.__proto__ || Object.getPrototypeOf(AsyncCreatableSelect)).apply(this, arguments));
	}

	createClass(AsyncCreatableSelect, [{
		key: 'focus',
		value: function focus() {
			this.select.focus();
		}
	}, {
		key: 'render',
		value: function render() {
			var _this2 = this;

			return React__default.createElement(
				Async,
				this.props,
				function (_ref) {
					var ref = _ref.ref,
					    asyncProps = objectWithoutProperties(_ref, ['ref']);

					var asyncRef = ref;
					return React__default.createElement(
						CreatableSelect,
						asyncProps,
						function (_ref2) {
							var ref = _ref2.ref,
							    creatableProps = objectWithoutProperties(_ref2, ['ref']);

							var creatableRef = ref;
							return _this2.props.children(_extends({}, creatableProps, {
								ref: function ref(select) {
									creatableRef(select);
									asyncRef(select);
									_this2.select = select;
								}
							}));
						}
					);
				}
			);
		}
	}]);
	return AsyncCreatableSelect;
}(React__default.Component);

var defaultChildren$1 = function defaultChildren(props) {
	return React__default.createElement(Select$1, props);
};

AsyncCreatableSelect.propTypes = {
	children: propTypes.func.isRequired // Child function responsible for creating the inner Select component; (props: Object): PropTypes.element
};

AsyncCreatableSelect.defaultProps = {
	children: defaultChildren$1
};

Select$1.Async = Async;
Select$1.AsyncCreatable = AsyncCreatableSelect;
Select$1.Creatable = CreatableSelect;
Select$1.Value = Value;
Select$1.Option = Option;

var clone_1 = createCommonjsModule(function (module) {
var clone = (function() {

function _instanceof(obj, type) {
  return type != null && obj instanceof type;
}

var nativeMap;
try {
  nativeMap = Map;
} catch(_) {
  // maybe a reference error because no `Map`. Give it a dummy value that no
  // value will ever be an instanceof.
  nativeMap = function() {};
}

var nativeSet;
try {
  nativeSet = Set;
} catch(_) {
  nativeSet = function() {};
}

var nativePromise;
try {
  nativePromise = Promise;
} catch(_) {
  nativePromise = function() {};
}

/**
 * Clones (copies) an Object using deep copying.
 *
 * This function supports circular references by default, but if you are certain
 * there are no circular references in your object, you can save some CPU time
 * by calling clone(obj, false).
 *
 * Caution: if `circular` is false and `parent` contains circular references,
 * your program may enter an infinite loop and crash.
 *
 * @param `parent` - the object to be cloned
 * @param `circular` - set to true if the object to be cloned may contain
 *    circular references. (optional - true by default)
 * @param `depth` - set to a number if the object is only to be cloned to
 *    a particular depth. (optional - defaults to Infinity)
 * @param `prototype` - sets the prototype to be used when cloning an object.
 *    (optional - defaults to parent prototype).
 * @param `includeNonEnumerable` - set to true if the non-enumerable properties
 *    should be cloned as well. Non-enumerable properties on the prototype
 *    chain will be ignored. (optional - false by default)
*/
function clone(parent, circular, depth, prototype, includeNonEnumerable) {
  if (typeof circular === 'object') {
    depth = circular.depth;
    prototype = circular.prototype;
    includeNonEnumerable = circular.includeNonEnumerable;
    circular = circular.circular;
  }
  // maintain two arrays for circular references, where corresponding parents
  // and children have the same index
  var allParents = [];
  var allChildren = [];

  var useBuffer = typeof Buffer != 'undefined';

  if (typeof circular == 'undefined')
    circular = true;

  if (typeof depth == 'undefined')
    depth = Infinity;

  // recurse this function so we don't reset allParents and allChildren
  function _clone(parent, depth) {
    // cloning null always returns null
    if (parent === null)
      return null;

    if (depth === 0)
      return parent;

    var child;
    var proto;
    if (typeof parent != 'object') {
      return parent;
    }

    if (_instanceof(parent, nativeMap)) {
      child = new nativeMap();
    } else if (_instanceof(parent, nativeSet)) {
      child = new nativeSet();
    } else if (_instanceof(parent, nativePromise)) {
      child = new nativePromise(function (resolve, reject) {
        parent.then(function(value) {
          resolve(_clone(value, depth - 1));
        }, function(err) {
          reject(_clone(err, depth - 1));
        });
      });
    } else if (clone.__isArray(parent)) {
      child = [];
    } else if (clone.__isRegExp(parent)) {
      child = new RegExp(parent.source, __getRegExpFlags(parent));
      if (parent.lastIndex) child.lastIndex = parent.lastIndex;
    } else if (clone.__isDate(parent)) {
      child = new Date(parent.getTime());
    } else if (useBuffer && Buffer.isBuffer(parent)) {
      if (Buffer.allocUnsafe) {
        // Node.js >= 4.5.0
        child = Buffer.allocUnsafe(parent.length);
      } else {
        // Older Node.js versions
        child = new Buffer(parent.length);
      }
      parent.copy(child);
      return child;
    } else if (_instanceof(parent, Error)) {
      child = Object.create(parent);
    } else {
      if (typeof prototype == 'undefined') {
        proto = Object.getPrototypeOf(parent);
        child = Object.create(proto);
      }
      else {
        child = Object.create(prototype);
        proto = prototype;
      }
    }

    if (circular) {
      var index = allParents.indexOf(parent);

      if (index != -1) {
        return allChildren[index];
      }
      allParents.push(parent);
      allChildren.push(child);
    }

    if (_instanceof(parent, nativeMap)) {
      parent.forEach(function(value, key) {
        var keyChild = _clone(key, depth - 1);
        var valueChild = _clone(value, depth - 1);
        child.set(keyChild, valueChild);
      });
    }
    if (_instanceof(parent, nativeSet)) {
      parent.forEach(function(value) {
        var entryChild = _clone(value, depth - 1);
        child.add(entryChild);
      });
    }

    for (var i in parent) {
      var attrs;
      if (proto) {
        attrs = Object.getOwnPropertyDescriptor(proto, i);
      }

      if (attrs && attrs.set == null) {
        continue;
      }
      child[i] = _clone(parent[i], depth - 1);
    }

    if (Object.getOwnPropertySymbols) {
      var symbols = Object.getOwnPropertySymbols(parent);
      for (var i = 0; i < symbols.length; i++) {
        // Don't need to worry about cloning a symbol because it is a primitive,
        // like a number or string.
        var symbol = symbols[i];
        var descriptor = Object.getOwnPropertyDescriptor(parent, symbol);
        if (descriptor && !descriptor.enumerable && !includeNonEnumerable) {
          continue;
        }
        child[symbol] = _clone(parent[symbol], depth - 1);
        if (!descriptor.enumerable) {
          Object.defineProperty(child, symbol, {
            enumerable: false
          });
        }
      }
    }

    if (includeNonEnumerable) {
      var allPropertyNames = Object.getOwnPropertyNames(parent);
      for (var i = 0; i < allPropertyNames.length; i++) {
        var propertyName = allPropertyNames[i];
        var descriptor = Object.getOwnPropertyDescriptor(parent, propertyName);
        if (descriptor && descriptor.enumerable) {
          continue;
        }
        child[propertyName] = _clone(parent[propertyName], depth - 1);
        Object.defineProperty(child, propertyName, {
          enumerable: false
        });
      }
    }

    return child;
  }

  return _clone(parent, depth);
}

/**
 * Simple flat clone using prototype, accepts only objects, usefull for property
 * override on FLAT configuration object (no nested props).
 *
 * USE WITH CAUTION! This may not behave as you wish if you do not know how this
 * works.
 */
clone.clonePrototype = function clonePrototype(parent) {
  if (parent === null)
    return null;

  var c = function () {};
  c.prototype = parent;
  return new c();
};

// private utility functions

function __objToStr(o) {
  return Object.prototype.toString.call(o);
}
clone.__objToStr = __objToStr;

function __isDate(o) {
  return typeof o === 'object' && __objToStr(o) === '[object Date]';
}
clone.__isDate = __isDate;

function __isArray(o) {
  return typeof o === 'object' && __objToStr(o) === '[object Array]';
}
clone.__isArray = __isArray;

function __isRegExp(o) {
  return typeof o === 'object' && __objToStr(o) === '[object RegExp]';
}
clone.__isRegExp = __isRegExp;

function __getRegExpFlags(re) {
  var flags = '';
  if (re.global) flags += 'g';
  if (re.ignoreCase) flags += 'i';
  if (re.multiline) flags += 'm';
  return flags;
}
clone.__getRegExpFlags = __getRegExpFlags;

return clone;
})();

if (module.exports) {
  module.exports = clone;
}
});

function styleInject(css, ref) {
  if ( ref === void 0 ) ref = {};
  var insertAt = ref.insertAt;

  if (!css || typeof document === 'undefined') { return; }

  var head = document.head || document.getElementsByTagName('head')[0];
  var style = document.createElement('style');
  style.type = 'text/css';

  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }

  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

var css = "/* stylelint-disable selector-pseudo-class-no-unknown */\n@font-face {\n  font-family: MSSansSerif;\n  src: url(\"data:application/octet-stream;base64,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\");\n  font-weight: normal; }\n\n@font-face {\n  font-family: MSSansSerif;\n  src: url(\"data:application/octet-stream;base64,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\");\n  font-weight: bold; }\n\nhtml {\n  font-size: 11px; }\n  html button {\n    font-size: 11px; }\n  html menu {\n    padding: 0px;\n    margin: 0px; }\n  html body {\n    font-family: MSSansSerif, \"Segoe UI\", Tahoma, Geneva, Verdana, sans-serif;\n    min-width: 200px;\n    margin: 0px; }\n  html .disabled {\n    color: #808088; }\n\n.w98 {\n  font-family: MSSansSerif, \"Segoe UI\", Tahoma, Geneva, Verdana, sans-serif;\n  width: 100%;\n  height: 100%;\n  image-rendering: pixelated;\n  position: relative;\n  transform: scale(1);\n  /* stylelint-disable selector-max-specificity */ }\n  .w98 *, .w98 {\n    font-family: MSSansSerif, \"Segoe UI\", Tahoma, Geneva, Verdana, sans-serif;\n    cursor: url(\"data:image/gif;base64,R0lGODlhCwATAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAALABMAAAIrhI4JlhrcBAgvSlrbxPBs7mAU9IlMaV7mwo6jY2zk+Xphh8iWint1tDgUAAA7\"), default; }\n    .w98 * .default, .w98 .default {\n      cursor: url(\"data:image/gif;base64,R0lGODlhCwATAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAALABMAAAIrhI4JlhrcBAgvSlrbxPBs7mAU9IlMaV7mwo6jY2zk+Xphh8iWint1tDgUAAA7\"), default; }\n    .w98 * .none, .w98 .none {\n      cursor: none; }\n    .w98 * .help, .w98 .help {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QAgQAGAAaYK/vaAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMcFDgJ8pMsJgAAANRJREFUWMPtlNsOhCAMRGf4/3+efdiFAIq02BiTpQkPau2c3iAAASD8psl3U8xkDOYVN8dMACDJA6FI0FQ8bRCKblVqPK8hVsSn/6aDp68dkMR8VsjSIKgJIouSbJ5vA3ggSGbfAhICYIE4EXfPCb86smTJ/l0NSlIrl9IQYFBOnlVpVfzQghNRdidUvAH4ibOa6MueRogXgCyOOKN3C9h24liFfk5WVm4EEJl52D0wrcJsdUMuotnd8MSw5DRZZxwl/gq7m4qi1vB1W7ABtm3b9j/2AXNCchMwrFvXAAAAAElFTkSuQmCC\"), help; }\n    .w98 * .pointer, .w98 .pointer {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAmklEQVRYhe2W0Q6AIAhFwfX/v0wPybLSaXqJHjhbWw8FR6CUqI7kyxyuJRc5cjNz6xkYyTJ4CKAETAdy62Y/B7KUgA3mqxaIiArBqjI9A4XIsoDQ5IoQEkkD1YJp/+/3SC4tGE2ClElExPmX64JWwE3i8RVY9XpEwKUKS3sBYru+C3xeBffdsLVc6Q0j6rT03wosvh8EQRAMswM0QjoRL/LEagAAAABJRU5ErkJggg==\"), pointer; }\n    .w98 * .progress, .w98 .progress {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAA0UlEQVRYhe2WUQ+DMAiE7xb//19mD6YbdiAwu/nCJSZG7fGFAhUABDeKCoDJNVnglN8GACICklKAgIjNQaYt9u93L9GLI4elGTgAVCCCDKTT8DCcgT8W5gfANxDVfQ8BMhAjKElMNbQGIIDgSfASxSlAFmJ+VtHmvTDSOc8JUYDeN6EOGTCCcrrc4Oq+1EEvgNG/AyIqQqvwvNkQAlSHx9AowhVtqB1SWdDBr0B4q87Oh+VngScPwqr+t2FxHrhtGOnKvlckuPmPqdVqtVqtn+sJVtRlLNr452EAAAAASUVORK5CYII=\"), progress; }\n    .w98 * .wait, .w98 .wait {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAsElEQVRYhe1Wuw7DMBDiqv7/L9OhcuRcLNXgNh56LM4QAeEeMVAo/DtCeJe/4H+qjORnHxHz37U9AcUAAFBIYIr7IRr4OmwDrc75vM0ASUTE6XQg90ATPwiSeJfEFLeT28WEKw54JYhebNADXjMYIN5jyfbskGwfQzeuYTM6nE4CJ/Em3JmRSrE8hhdCMQk5gSyeN6C6kJaasN+ELpb+BXkd32ZgJO6a2H4hqStZofACqCxSMK3nScIAAAAASUVORK5CYII=\"), wait; }\n    .w98 * .crosshair, .w98 .crosshair {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAcklEQVRYhe2VQQrAIAwEk9L/f3l7UahCGs0WvOxchOKmEzBqJoQgAIC2oFrj+tFHAhKQQAkn8+/5L9UKQ9nl4u5zPr2PvIWWBGzsLqwJoMss7Z8/3OHf826GdSfzabQJfQaoKegdE2/R+TGUgAQkIMRxHuP5JBvfrnY7AAAAAElFTkSuQmCC\"), crosshair; }\n    .w98 * .text, .w98 .text {\n      cursor: url(\"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAkAAAASAgMAAAD07hzbAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAJUExURQAAAP///wAAAHPGg3EAAAABdFJOUwBA5thmAAAAIElEQVQI12MIFXVgyNJyYAid6sDAOIGBJAzSA9Yr6gAAtPsMHZZ0H8cAAAAASUVORK5CYII=\"), text; }\n    .w98 * .vertical-text, .w98 .vertical-text {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAADsMAAA7DAcdvqGQAAAAZdEVYdFNvZnR3YXJlAHBhaW50Lm5ldCA0LjAuMjHxIGmVAAAAa0lEQVRYR+3S4QqAMAgEYPf+7+xSM4n9Sh0FcR+MjejcEdFqzsmyLsMfPyLvW5bZtlQ2aF63ypBONnSGdLJhGZLmWQ3XCtxYkcIacn/9cmm+4wvo8R//wDcFNO3SBc6Y7bUCAAAAAADwLqIDkiY1rkgTay4AAAAASUVORK5CYII=\"), vertical-text; }\n    .w98 * .alias, .w98 .alias {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBDI7ZDFROQAAANNJREFUWMPFluEOhSAIhc9hvf8rc//oVlxIKwW3ZonjfCJiAKAobNJ6LQVQ1TKIHoEyCDl/VECIHciGEG8wE0IiQxaE3BkzIGQ0YTfEERlI/rEA4NYIOKI0z74taOLsEKlJ2MUrSzGvO8HUU1Cy8ru7AKrqRuFkX0/iONfe2jvSIMzZV5sHWeJL54cFzzp1ihFe/LZNJ/YxKT696pGPEIDkFEQk9HZLxEZgNttX5YB4EfD6r6F+dBtGvSf+NRKyuHjlASzPgafiW3KgvBKONDf5rW0/WMag8gddiAEAAAAASUVORK5CYII=\"), alias; }\n    .w98 * .copy, .w98 .copy {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBAUOooU1LgAAANBJREFUWMPFluEOhSAIhQ+s93/lc//oZlw1LQG2ZomDD0QSAIhE0TIyFYBkGkTNQBqEth8ZEGonoiG0NxkJoSNFFITOlBEQ+rTAG+IaKUTkjwWAuGag41TM47cFxblUiNAirM4zW7Hcd0JCT0FK5LN/AUh2s9Doz5N0jLNKeUcYhDn7tHUQ5fzo+mHDs0Y7zQgvrm3LhX0tOl+O+snGtBO67O3OnbCFWKn23WiXMjAavUT2Cp/DyI1uvwjfHMET2VEkyyeAE7WRnoGtInSymys/pBqY6woaqXMAAAAASUVORK5CYII=\"), copy; }\n    .w98 * .move, .w98 .move {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAA2ElEQVRYhdWU4Q7DIAiED7P3f2X2Rw0Fqm4rkF1iotT0vh5VAOA+StQAgJlRBdHGpAqiyUUFRNOFbAgDkA3hAmRC3AJkQSwBMiC2ANEQr9VDIjIsAEzxF5kEHFNS41FdABzzcE2Abk4SJO0USHMExLwFcEwpK4XmmB+JO1m0eAgihbF+AuLoItJEoz1ElJLE/HqRxGWEQ0gD2RIxN/ueNveMtrUTLU+A7Ld+b++/qY29dHit3m6S5t/oFKI8ga2i/4FPIOY89RQ4IPn3wAoi1VxDlJgriP/XG6yaCnPXsXLdAAAAAElFTkSuQmCC\"), move; }\n    .w98 * .no-drop, .w98 .no-drop {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBRwLSC0CjgAAAXdJREFUWMPFlsGOwyAMRGfQKh/dw4r+WX+rp9nDhsoBG0LbJEiREiD28wA2AKD1uaQlAJCEqyBSebkKItmPKyBS3XE2RPI6z4RI0cBZEKk3eAZEGk04GiLtmXQkxE9vkGTDAoCHKuA4ZfUcp4DjfKppXSsnqNAwy3/rHJa1LrZM/9Bx5MfYcuWVeW+CGQFI0l7l1kDpAbCnaAThOa9XwRvnTmKV5h1B0y87974srpF67sy+aiBqgxsIABmAB/IORAMgaWPMVWL9yB3VplSInDuADYRVwpu3JxVTEqMNBYAgaQMiudmNOefyPycC3+5qSbgvSyPjqsqrw1MiUmGogElQe0iLWqES0xcS6zwEqfud5fh9PjUNQHID7wXiRii5EGW96kDSqBw3jqONZA0HEF5GHJ6CAkESut1498u33oF4p9z+n4ROKlbJFyYPfJKKm/Z4PFIEsQGR9GkdGELkTl2IasXXrlKSkHNmkbgHYsbdG9E3oaavZH/EPvZcdfrYzAAAAABJRU5ErkJggg==\"), no-drop; }\n    .w98 * .not-allowed, .w98 .not-allowed {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAy0lEQVRYhe2W4QrEMAiD473/O2e/eoxW29gTjrEGBoNZ/WY6O+Do6O2ynUUk6SYzS+dLLWiFozqNKwMiB5KkmpekDCEFecV7F7znCsQyoC8etdmzJ9OJsDiA4Yo2obdmFgsAnwTM997Mpl/CoqYGsPJ9BtEBTeOkDjQv+7eLkme6IFsQJVc7UQZQDbEFUAkhAahet7jM1AwB1I3kQdy1GkayBZlv/5fhN8ibbBFIdgoChYcRsHcOPOM4vkMAf/oh8UCGZKW77+joLboA0XnR6i7uxKYAAAAASUVORK5CYII=\"), not-allowed; }\n    .w98 * .grab, .w98 .grab {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAnElEQVRYhe2W0QqAIAxFXfT/v7we0pBK3L1OpNiBXgzccXOrlIKPovkZRpjgqmdsEWH3uNiRwJ11SmSzBlfVVE5+e1HWqZJYBazAd8NVgMmGdwZglgu0uqBO4VCbMQJa33YRcRk4LeAS1HJvbekhIHnCQUFYmVYGKAlPgYfELCwRFMkA+oFaPgcsAlNLgezcLQXzf/CJEgRBEPybA/IvPA8uFeG1AAAAAElFTkSuQmCC\"), grab; }\n    .w98 * .grabbing, .w98 .grabbing {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAc0lEQVRYhe2TUQrAIAxD27H7X7n7mIPSWSsjbvvIA6EikrRGEULuWFujGoZGcbNTQ1Ulq5O7j9iyg0sw1m4PmUY0oK7D0tgKA/A3rti9OLq7GdIM/NpAywn8F5QBXEFPcZgFZPci/Sd4dRKfh5AQQggh5AAdUSYPeo+oPgAAAABJRU5ErkJggg==\"), grabbing; }\n    .w98 * .col-resize, .w98 .col-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAl0lEQVRYhe2UwQ7AIAhD7f7/n7vD1HhARFnizHgnoxYaQFMKgmAz8IhJsgYClmJdHgM5sUvvNuDlDANtr61YNUMDJAlgysSMRp2gEiiv5QBPInG/6LQX0j1okyt3qgHtrmZCbIEl+QxaO0QDALAwd120CmyfgSG5dJRK2DvTNB4TK+aGmD6ilRJaNWd8xZ828OZzDYLgn9xKNn/lGRmPWwAAAABJRU5ErkJggg==\"), col-resize; }\n    .w98 * .row-resize, .w98 .row-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAhklEQVRYhe2WSwrAIAxEJ6X3v/J0FZBC1GhosGTAnfqef4FK5eSQZDacKRIK1/KpxBu+KyFeuIjdhCSkV2FXQCUAoOXo4L1wALi8DSzICnxJIDrpAt1pizheo6W5JzpYhs/4DwUyb1szkTdh+iYsAbeAtd7HPkbuRD/HIRKpv6LUf2Gl8os8sq93x5ioZpYAAAAASUVORK5CYII=\"), row-resize; }\n    .w98 * .n-resize, .w98 .n-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBBgJw43MkQAAAFtJREFUWMPtlkEKgDAQAzfi/78cT6UgUtAt5jIDPXUhQ0lhqwCggW2nwx2RGOHj/CpxD+9K6G24pNV9aTXwwPnhBaa9VLEe7irhkf7KCCCAAAIItASSCxEAbOMCMNw96tMgkUMAAAAASUVORK5CYII=\"), n-resize; }\n    .w98 * .e-resize, .w98 .e-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBBsyWat2dgAAAFlJREFUWMPt00EOwCAIRNEZ4/2vbDd1W8UUTdP/DuAAggQA+Ip2e/vdMhtuO6WxcjJckhwJX/0BP3RQI52vTGJU9PEJTC2gpNYPYfsS2nZCbuwMs4sAAPzbBds9NPzhUi4sAAAAAElFTkSuQmCC\"), e-resize; }\n    .w98 * .s-resize, .w98 .s-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBBkAo0pFdAAAAF9JREFUWMPtlTEKACEMBI34/y/vNSKiyGEM2syAhYW7ExCSEgA8xrwPJamFmLlz8pG9vzdGIAIEEEAAAQSKdwFFLaayazzm9/eFXyx12unoSvtC4mr5KPGk/O9TAsAOHynIM/9dczKqAAAAAElFTkSuQmCC\"), s-resize; }\n    .w98 * .w-resize, .w98 .w-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMdBBcwGxBYVgAAAF5JREFUWMPt00EKwCAMBdGJ9P5XtpsKbtrGQhDKvKWo+YYIkqS/6Zfs/lYRIiLIhmhVnciGiLd2fi0+3UHMC6sBHs6uzMVtiCNzuLIDJb8A6ONDbBvC7MvbzuKSJAGcm3Yz/tgKV5oAAAAASUVORK5CYII=\"), w-resize; }\n    .w98 * .ns-resize, .w98 .ns-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAcElEQVRYhe2VwQrAIAxDm7H//+XsVBCZg2K1E/LAg1JNDqk1E0KcDElWi7PEhIv72mqiF581gag4ML5C0vBV8MIdKXYRB4CV5TArhFeSHxk410CoC0aBa8+Xt2H/frvf0pLZP2GKidKB9IeRLIQQUzyny2q/gqNGmAAAAABJRU5ErkJggg==\"), ns-resize; }\n    .w98 * .ew-resize, .w98 .ew-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAADsMAAA7DAcdvqGQAAAAZdEVYdFNvZnR3YXJlAHBhaW50Lm5ldCA0LjAuMjHxIGmVAAAAaUlEQVRYR+3O4QrAIAgEYN//pTcZF5RkbdN+FPdBlChnQkRE27kAZQOtbi8Fwt0ls35ICcdz+AE8uzO/1MEoXXZO7xgb+vUs+cSIndM7Rx3uBb+ZCSkLvPBZP8WTrlA20Fq3nIiIDiRyAzGq1ipFTm7RAAAAAElFTkSuQmCC\"), ew-resize; }\n    .w98 * .ne-resize, .w98 .ne-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAACxIAAAsSAdLdfvwAAAAHdElNRQfgAx0EGAnDjcyRAAAAGXRFWHRTb2Z0d2FyZQBwYWludC5uZXQgNC4wLjIx8SBplQAAAQhJREFUWEftkjELgkAYhoXanQrbXaIpcQwaQ2q2scXJyQY3B6HVMWhs6wdEv8TBwSVwcY4L2vx6z06IaGjwCuIeeOFTX+75kNMUCoXiLyCiOTJExsgCmSADZCYq8oBkXRQF+b5/DYLgliQJRVFEnuddyrLci5o8sMAUYa7rEn9sYts2XtMJ6fKeVMQSt+clDMOgPM93dUE2kPM7QI7jkGma9QK6rlOapttHQyLPctwDPlb8T1iWxecj0hHV9sHhr/IzskJYHMfEGDuIavtA8k4+Et/qi4ks63Lb4OB5VVVv5Q147omxXT6RS0PJfyLnQLbJsozCMPy+vIEv8TN5A+R9MSoUin9B0+7KtTA+X83ffwAAAABJRU5ErkJggg==\"), ne-resize; }\n    .w98 * .nw-resize, .w98 .nw-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAACxIAAAsSAdLdfvwAAAAHdElNRQfgAx0EGAnDjcyRAAAAGXRFWHRTb2Z0d2FyZQBwYWludC5uZXQgNC4wLjIx8SBplQAAAPtJREFUWEftkiFrw0AYhgOdj1pJfUyZaogcTI7Q6kzOREWlIi4iMBtZmJzrDxj7JRERMYWY6JFBXL6+X7krtP6uK3wPPOSOfPC+x50jCILw7yGiV7iAz3ADV3AJ12rELH3ffyVJ8lsUBVVVRVmWjWma/nVdhw60VWNmQMAD/AnDkHirjeOYwwf4wnNGadv20/O86/DRSjhT1/XOdd1TuO/7FEURF2DMvwGEzOB3EAT65BPu326JYRj2ZVlyGN/5OzxYLYGAN3h+cPg+QeslHtXyBPYXJaZpMl/iGimhkRIaXSLPc2qahgt8qF/20CVuEq5B+FwtBUG4BxznCFyoMD4Owsf7AAAAAElFTkSuQmCC\"), nw-resize; }\n    .w98 * .se-resize, .w98 .se-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAACxIAAAsSAdLdfvwAAAAHdElNRQfgAx0EGAnDjcyRAAAAGXRFWHRTb2Z0d2FyZQBwYWludC5uZXQgNC4wLjIx8SBplQAAAQpJREFUWEftkiFrw1AUhQObj1pJfUypWogcVJbQ6UzWREWlIi4iMBtZqKzrDyj9JRERMYOY6PIGdbk7N32UMiJmXtvB/eCQ+y4Hznm8WIIg/CuIaKTH24PwT+gLmurV7eDwqqooTVOMdyiBwEXXdRQEAcVxLCWkxJ9K4PyiRzNwCU4eKoHvDFLQR282BQKGSiwhlec5KaV22moOhP0u0YVhSJ7n8byHnrTVHAi5lHBdl3hl2zaVZbk+OwyDbH7zE9+cjyzHcaiu601vMIkOV9fhLN/3saYD9Mw+YyBg1TQNv/93kiSnoigoyzKKoujYtu1W28yCEvwPTKBX6B16g8bQXFsEQRAeFcv6AdG5MD4EgcmOAAAAAElFTkSuQmCC\"), se-resize; }\n    .w98 * .sw-resize, .w98 .sw-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAAXNSR0IArs4c6QAAAARnQU1BAACxjwv8YQUAAAAJcEhZcwAACxIAAAsSAdLdfvwAAAAHdElNRQfgAx0EGAnDjcyRAAAAGXRFWHRTb2Z0d2FyZQBwYWludC5uZXQgNC4wLjIx8SBplQAAAP9JREFUWEftki1rw1AUhgOrj1pJfcyYWogsVI6w6VTWREVlIi4iUBtZqJzrDxj7JRERMYOY6HILdffsveGk0B9wjyj3gQdOPrjvy+V4Dofj4SCiJY/yIPwV/sE9v5JjDi/LkrquwyhYYg7P85ySJCGttSnwwZ/t4sJFwnHwM48T0uFbqOCGn+/CGXvXrpQ61XVtQkyJHZQLx+FP8CeKIkrT1IRpsfCZtm0Pvu8TRgrDUDbc0Pf9MQiCqYCRb+IKp52wCkIW8DeO41sBI5e4LaZVxnH8zrLsXFUVNU1DRVFcsQeXYRhMiS/+zR4IeYcruIaf8A2+QJkdcDgcDrt43j9jrDA+BfthpgAAAABJRU5ErkJggg==\"), sw-resize; }\n    .w98 * .nesw-resize, .w98 .nesw-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAfUlEQVRYhe2UOQ6AMAwEs4j/f3lpQDJHDmKHFOx0pPCMcpCSEEJMBt4BJJkdDlTnr96AXXRbK3SdWALkaJUNCfBGhASQJIDmbQ8NsHLvcVRF1xu/fz+ul15Hd4CV5eTDOIRGGiLvugP2zKcEmIg5OxAZ8epX/NV9E0KIf7EB3G1l2PEHnRoAAAAASUVORK5CYII=\"), nesw-resize; }\n    .w98 * .nwse-resize, .w98 .nwse-resize {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAAfUlEQVRYhe2UQQrAIAwEk9L/f3l7UZBiJCZqD925KTE7AVWEEEI+Rj1FAGA2UHX1sLi9hb2cgZebK3oQQHr6sMCq8JBACR/ei20CdfLVEp5gvMPKurt/VKyVsKROSkwLhJ9hpb0TEdICAJB5kSmBbLjIxFc8kMi2IISQn/MAfiVl2DaxoY4AAAAASUVORK5CYII=\"), nwse-resize; }\n    .w98 * .zoom-in, .w98 .zoom-in {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMcFSIpeBKcAgAAAKRJREFUWMPtlUsSgCAMQxvH+185btQBLH5oRUf7dspgYiityN/BwTob95kNUESE1PUBuBnRPsBUOBGT0tS8Bk8Dq/giXKZQvreaGGsRaymQzIRrR3SFoRb9WeY99DCw+TMAWQ2kzyQ39eFioDeDFql25j1qAC2R3nIL9lKoXc8nG5EpAWsrNs8H6zCi1YTHVDOZ8BqrzSa8GhEk+DReXS8IguCVTDaGYBOde5IGAAAAAElFTkSuQmCC\"), zoom-in; }\n    .w98 * .zoom-out, .w98 .zoom-out {\n      cursor: url(\"data:image/png,base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAAsTAAALEwEAmpwYAAAAB3RJTUUH4AMcFTE76kSs2AAAAKRJREFUWMPtVVsOgCAM2wz3v3L9AbMQhshGJLp+yqNdZR3R38E365g8ZxYAIiKgzc/MbkJaF0ASCzKqReU19hRwkRfi2oX6u1VE0izW7JfE2p4nODTrR5HPwM0BWVn9/yUpABcXjrdzILWqK5X1qlvxBlizvNtGK7qguDDShjsEkckBaxSb54N1GMEqwmOqmUR4jdVpEV5BxBT4NLxSLxAIBLbECVu1WhFGEEeXAAAAAElFTkSuQmCC\"), zoom-out; }\n  .w98.x2 {\n    transform: scale(2); }\n    .w98.x2 *, .w98.x2 {\n      cursor: url(\"data:image/gif;base64,R0lGODlhFgAmAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAWACYAAAJzBISpu8b/jINUHgpNCBMrzV1eAm6dV4YjkppiBWyyisazfDIt/ur2zcv8gDQf8ZYT7IDJJfHkZL6izwtVyhpKLVwtssudpZJZ8ZCstE3GvbSrHGxIPue2hW72CfOkNvy9wrbiFjcoGFhnmIjIp4iGcZdQAAA7\"), default; }\n  .w98 ::-webkit-scrollbar {\n    width: 16px;\n    height: 16px;\n    background-color: #ffffff;\n    background-image: url(\"data:image/gif;base64,R0lGODlhAgACAJEAAAAAAP///8zMzP///yH5BAEAAAMALAAAAAACAAIAAAID1CYFADs=\"); }\n    .w98 ::-webkit-scrollbar-track {\n      position: relative; }\n    .w98 ::-webkit-scrollbar-thumb {\n      background: #bbc3c4;\n      box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px 0px #ffffff;\n      border: 1px solid #0c0c0c;\n      border-top: 1px solid #bbc3c4;\n      border-left: 1px solid #bbc3c4; }\n    .w98 ::-webkit-scrollbar-button {\n      background: #bbc3c4;\n      box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px 0px #ffffff;\n      border: 1px solid #0c0c0c;\n      border-top: 1px solid #bbc3c4;\n      border-left: 1px solid #bbc3c4; }\n      .w98 ::-webkit-scrollbar-button:start:decrement, .w98 ::-webkit-scrollbar-button:end:increment {\n        height: 16px;\n        width: 16px;\n        display: block;\n        background-repeat: no-repeat;\n        background-color: #bbc3c4; }\n        .w98 ::-webkit-scrollbar-button:start:decrement:active, .w98 ::-webkit-scrollbar-button:end:increment:active {\n          border: 1px solid #808088;\n          box-shadow: none;\n          background-color: #bbc3c4; }\n      .w98 ::-webkit-scrollbar-button:horizontal:decrement {\n        background-image: url(\"data:image/gif;base64,R0lGODlhBAAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAEAAcAAAIIlHEIy7ppBCgAOw==\");\n        background-position: 4px 3px; }\n        .w98 ::-webkit-scrollbar-button:horizontal:decrement:active {\n          background-position: 5px 4px; }\n      .w98 ::-webkit-scrollbar-button:horizontal:increment {\n        background-image: url(\"data:image/gif;base64,R0lGODlhBAAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAEAAcAAAIIhA4maeyrlCgAOw==\");\n        background-position: 5px 3px; }\n        .w98 ::-webkit-scrollbar-button:horizontal:increment:active {\n          background-position: 6px 4px; }\n      .w98 ::-webkit-scrollbar-button:vertical:decrement {\n        background-image: url(\"data:image/gif;base64,R0lGODlhBwAEAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAHAAQAAAIHlGEJq8sOCwA7\");\n        background-position: 3px 5px; }\n        .w98 ::-webkit-scrollbar-button:vertical:decrement:active {\n          background-position: 4px 6px; }\n      .w98 ::-webkit-scrollbar-button:vertical:increment {\n        background-image: url(\"data:image/gif;base64,R0lGODlhBwAEAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAHAAQAAAIIhA+CKWoNmSgAOw==\");\n        background-position: 3px 5px; }\n        .w98 ::-webkit-scrollbar-button:vertical:increment:active {\n          background-position: 4px 6px; }\n    .w98 ::-webkit-scrollbar-corner {\n      /*\n      background-image: url(resources/corner.png);\n      background-repeat: no-repeat;\n      */\n      background-color: #bbc3c4; }\n  .w98 ::selection {\n    color: #ffffff;\n    background-color: #0000a2; }\n";
styleInject(css);

var Theme = function Theme(props) {
  return React__default.createElement("div", {
    className: cx('w98', props.className),
    style: props.style
  }, props.children);
};

Theme.propTypes = {
  children: propTypes.node,
  className: propTypes.string,
  style: propTypes.shape()
};

function _typeof$1(obj) {
  if (typeof Symbol === "function" && typeof Symbol.iterator === "symbol") {
    _typeof$1 = function (obj) {
      return typeof obj;
    };
  } else {
    _typeof$1 = function (obj) {
      return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
    };
  }

  return _typeof$1(obj);
}

function _classCallCheck(instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
}

function _defineProperties(target, props) {
  for (var i = 0; i < props.length; i++) {
    var descriptor = props[i];
    descriptor.enumerable = descriptor.enumerable || false;
    descriptor.configurable = true;
    if ("value" in descriptor) descriptor.writable = true;
    Object.defineProperty(target, descriptor.key, descriptor);
  }
}

function _createClass(Constructor, protoProps, staticProps) {
  if (protoProps) _defineProperties(Constructor.prototype, protoProps);
  if (staticProps) _defineProperties(Constructor, staticProps);
  return Constructor;
}

function _defineProperty(obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value: value,
      enumerable: true,
      configurable: true,
      writable: true
    });
  } else {
    obj[key] = value;
  }

  return obj;
}

function _extends$1() {
  _extends$1 = Object.assign || function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];

      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }

    return target;
  };

  return _extends$1.apply(this, arguments);
}

function _objectSpread(target) {
  for (var i = 1; i < arguments.length; i++) {
    var source = arguments[i] != null ? arguments[i] : {};
    var ownKeys = Object.keys(source);

    if (typeof Object.getOwnPropertySymbols === 'function') {
      ownKeys = ownKeys.concat(Object.getOwnPropertySymbols(source).filter(function (sym) {
        return Object.getOwnPropertyDescriptor(source, sym).enumerable;
      }));
    }

    ownKeys.forEach(function (key) {
      _defineProperty(target, key, source[key]);
    });
  }

  return target;
}

function _inherits(subClass, superClass) {
  if (typeof superClass !== "function" && superClass !== null) {
    throw new TypeError("Super expression must either be null or a function");
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      writable: true,
      configurable: true
    }
  });
  if (superClass) _setPrototypeOf(subClass, superClass);
}

function _getPrototypeOf(o) {
  _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf : function _getPrototypeOf(o) {
    return o.__proto__ || Object.getPrototypeOf(o);
  };
  return _getPrototypeOf(o);
}

function _setPrototypeOf(o, p) {
  _setPrototypeOf = Object.setPrototypeOf || function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };

  return _setPrototypeOf(o, p);
}

function _objectWithoutPropertiesLoose(source, excluded) {
  if (source == null) return {};
  var target = {};
  var sourceKeys = Object.keys(source);
  var key, i;

  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }

  return target;
}

function _objectWithoutProperties(source, excluded) {
  if (source == null) return {};

  var target = _objectWithoutPropertiesLoose(source, excluded);

  var key, i;

  if (Object.getOwnPropertySymbols) {
    var sourceSymbolKeys = Object.getOwnPropertySymbols(source);

    for (i = 0; i < sourceSymbolKeys.length; i++) {
      key = sourceSymbolKeys[i];
      if (excluded.indexOf(key) >= 0) continue;
      if (!Object.prototype.propertyIsEnumerable.call(source, key)) continue;
      target[key] = source[key];
    }
  }

  return target;
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return self;
}

function _possibleConstructorReturn(self, call) {
  if (call && (typeof call === "object" || typeof call === "function")) {
    return call;
  }

  return _assertThisInitialized(self);
}

function _toConsumableArray(arr) {
  return _arrayWithoutHoles(arr) || _iterableToArray(arr) || _nonIterableSpread();
}

function _arrayWithoutHoles(arr) {
  if (Array.isArray(arr)) {
    for (var i = 0, arr2 = new Array(arr.length); i < arr.length; i++) arr2[i] = arr[i];

    return arr2;
  }
}

function _iterableToArray(iter) {
  if (Symbol.iterator in Object(iter) || Object.prototype.toString.call(iter) === "[object Arguments]") return Array.from(iter);
}

function _nonIterableSpread() {
  throw new TypeError("Invalid attempt to spread non-iterable instance");
}

var css$1 = ".btn {\n  border: 0px solid transparent;\n  background-color: #bbc3c4;\n  position: relative;\n  user-select: none; }\n  .btn:disabled, .btn.disabled {\n    pointer-events: none; }\n  .btn:active, .btn:focus, .btn:active:focus, .btn.active, .btn.clicked {\n    outline: none;\n    color: inherit; }\n  .btn:before {\n    position: absolute;\n    display: block;\n    top: 1px;\n    left: 1px;\n    width: calc(100% - 2px);\n    height: calc(100% - 2px); }\n";
styleInject(css$1);

var AbstractButton =
/*#__PURE__*/
function (_Component) {
  _inherits(AbstractButton, _Component);

  function AbstractButton() {
    var _getPrototypeOf2;

    var _this;

    _classCallCheck(this, AbstractButton);

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(AbstractButton)).call.apply(_getPrototypeOf2, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this), "state", {
      mouseDown: false
    });

    _defineProperty(_assertThisInitialized(_this), "handleMouse", function (func, mouseDown) {
      _this.setState({
        mouseDown: mouseDown
      });

      if (func) {
        func();
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleClick", function (e) {
      _this.button.focus();

      if (_this.props.onClick) {
        _this.props.onClick(e);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleBlur", function (e) {
      if (_this.props.onBlur) {
        _this.props.onBlur(e);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleContextMenu", function (e) {
      e.preventDefault();
      e.stopPropagation();

      _this.button.focus();

      if (_this.props.onContextMenu) {
        _this.props.onContextMenu(e);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleDoubleClick", function (e) {
      if (_this.props.onDoubleClick) {
        _this.props.onDoubleClick(e);
      }
    });

    return _this;
  }

  _createClass(AbstractButton, [{
    key: "render",
    value: function render() {
      var _this2 = this;

      var props = this.props;
      return React__default.createElement("button", {
        ref: function ref(btn) {
          _this2.button = btn;
        },
        className: cx('btn', props.className, {
          clicked: this.state.mouseDown,
          'btn--active': props.isActive,
          'btn--disabled': props.isDisabled
        }),
        onClick: function onClick(e) {
          return _this2.handleClick(e);
        },
        onDoubleClick: function onDoubleClick(e) {
          return _this2.handleDoubleClick(e);
        },
        onMouseDown: function onMouseDown() {
          return _this2.handleMouse(props.onMouseDown, true);
        },
        onMouseUp: function onMouseUp() {
          return _this2.handleMouse(props.onMouseUp, false);
        },
        onBlur: function onBlur(e) {
          return _this2.handleBlur(e);
        },
        onContextMenu: this.props.onContextMenu && function (e) {
          return _this2.handleContextMenu(e);
        },
        disabled: props.isDisabled,
        style: props.style,
        title: props.title
      }, props.children);
    }
  }]);

  return AbstractButton;
}(React.Component);

var commonButtonPropTypes = {
  children: propTypes.oneOfType([propTypes.string, propTypes.node]),
  title: propTypes.string,
  className: propTypes.string,
  isActive: propTypes.bool,
  isDisabled: propTypes.bool,
  onBlur: propTypes.func,
  onClick: propTypes.func
};
AbstractButton.propTypes = _objectSpread({}, commonButtonPropTypes, {
  onDoubleClick: propTypes.func,
  onContextMenu: propTypes.func,
  onMouseDown: propTypes.func,
  onMouseUp: propTypes.func,
  style: propTypes.shape() // Todo: Needs custom prop

});

var commonButtonPropTypes$1 = AbstractButton.propTypes;

var css$2 = ".btn.ButtonForm {\n  min-width: 48px;\n  outline-width: 1px;\n  outline-offset: -5px;\n  padding: 5px 1px;\n  box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #ffffff, inset -2px -2px 0px #808088, inset 2px 2px 0px #bbc3c4; }\n  .btn.ButtonForm:focus {\n    outline: #0c0c0c;\n    outline-style: dotted;\n    outline-width: 1px;\n    box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #0c0c0c, inset -2px -2px 0px #0c0c0c, inset 2px 2px 0px #ffffff; }\n  .btn.ButtonForm:active:focus, .btn.ButtonForm:active, .btn.ButtonForm.active, .btn.ButtonForm.clicked {\n    padding: 6px 0px 4px 2px;\n    box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #0c0c0c, inset -2px -2px 0px #808088, inset 2px 2px 0px #808088; }\n";
styleInject(css$2);

var ButtonForm = function ButtonForm(props) {
  return React__default.createElement(AbstractButton, {
    className: cx('ButtonForm', props.className),
    onClick: props.onClick,
    isActive: props.isActive,
    isDisabled: props.isDisabled
  }, props.children);
};

AbstractButton.propTypes = _objectSpread({}, commonButtonPropTypes$1);

var css$3 = ".btn.ButtonNav {\n  padding: 0px;\n  min-width: initial;\n  width: 16px;\n  height: 14px;\n  margin-left: 1px;\n  margin-top: 1px;\n  margin-bottom: 2px;\n  image-rendering: pixelated;\n  box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #ffffff, inset -2px -2px 0px #808088, inset 2px 2px 0px #bbc3c4; }\n  .btn.ButtonNav img {\n    height: 14px;\n    width: 14px; }\n  .btn.ButtonNav:focus {\n    outline: none;\n    border: none; }\n  .btn.ButtonNav:active:focus, .btn.ButtonNav.clicked {\n    padding-top: 2px;\n    padding-bottom: 1px;\n    padding-left: 4px;\n    padding-right: 8px;\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #0c0c0c, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px #808088; }\n  .btn.ButtonNav.window__close, .btn.ButtonNav.Window__close {\n    margin-left: 2px; }\n";
styleInject(css$3);

var ButtonNav = function ButtonNav(props) {
  return React__default.createElement(AbstractButton, {
    className: cx('ButtonNav', props.className),
    onClick: props.onClick,
    isActive: props.isActive,
    isDisabled: props.isDisabled
  });
};

ButtonNav.propTypes = commonButtonPropTypes$1;

var css$4 = ".btn.ButtonProgram {\n  flex: 1;\n  margin: 0px 1px;\n  height: 22px;\n  max-width: 140px;\n  min-width: 40px;\n  display: inline-block;\n  width: 100%;\n  padding-top: 1px;\n  padding-left: 22px;\n  padding-right: 3px;\n  text-align: left;\n  overflow: hidden;\n  white-space: nowrap;\n  text-overflow: ellipsis;\n  background-size: 16px;\n  background-repeat: no-repeat;\n  background-position: 4px 4px;\n  box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #ffffff, inset -2px -2px 0px #808088, inset 2px 2px 0px #bbc3c4; }\n  .btn.ButtonProgram:active:focus, .btn.ButtonProgram.btn--active, .btn.ButtonProgram.clicked {\n    background-position: 5px 5px;\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #0c0c0c, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px #808088;\n    padding-top: 3px;\n    padding-left: 23px;\n    padding-right: 2px; }\n    .btn.ButtonProgram:active:focus:before, .btn.ButtonProgram.btn--active:before, .btn.ButtonProgram.clicked:before {\n      content: \"\";\n      background-size: 2px;\n      z-index: -1;\n      box-shadow: none; }\n  .btn.ButtonProgram.btn--active {\n    background-color: transparent;\n    font-weight: bold; }\n    .btn.ButtonProgram.btn--active:before {\n      content: \"\";\n      background-color: #ffffff;\n      background-image: url(\"data:image/gif;base64,R0lGODlhAgACAJEAAAAAAP///8zMzP///yH5BAEAAAMALAAAAAACAAIAAAID1CYFADs=\"); }\n";
styleInject(css$4);

var ButtonProgram = function ButtonProgram(props) {
  return React__default.createElement(AbstractButton, {
    className: cx('ButtonProgram', props.className),
    onClick: props.onClick,
    isActive: props.isActive,
    style: _objectSpread({
      backgroundImage: "url(".concat(props.icon, ")")
    }, props.style)
  }, props.children);
};

ButtonProgram.propTypes = _objectSpread({}, commonButtonPropTypes$1, {
  icon: propTypes.any
});

var css$5 = ".btn.StartButton {\n  height: 22px;\n  display: flex;\n  align-content: center;\n  width: 54px;\n  padding-right: 6px;\n  background-image: url(\"data:image/gif;base64,R0lGODlhNAATAKIAAAAAAP///wAA/wD/AP//AP8AAP///wAAACH5BAEAAAYALAAAAAA0ABMAAAOPaLrc/jDKSaudIIPLu95dKH2fGIKLVmSDxpTms83qCgwtmik7j46/BglQsOF6BuQrCFEuCkLiJ5diJnswl6sB7dqGSpjPscNaFcWiRpAhbKPVqhbkVAiiAjaA4LYizWOADneEenltfXFXioCCD3mHAHptYW9jV3OKL1FgZzEySZiVnp8yYkKlFyRNqa2uEgkAOw==\");\n  background-size: auto 18px;\n  background-repeat: no-repeat;\n  background-position: 2px 1px;\n  box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #ffffff, inset -2px -2px 0px #808088, inset 2px 2px 0px #bbc3c4; }\n  .btn.StartButton__text {\n    font-size: 1rem;\n    font-weight: bold; }\n  .btn.StartButton.active, .btn.StartButton.clicked {\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #0c0c0c, inset 0px 1px 0px #0c0c0c, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px #808088, 0px -1px 0px #0c0c0c;\n    background-position: 3px 2px;\n    outline: 1px dotted #0c0c0c;\n    outline-offset: -4px; }\n";
styleInject(css$5);

var StartButton = function StartButton(props) {
  return React__default.createElement(AbstractButton, {
    className: cx('StartButton', props.className),
    onClick: props.onClick,
    onBlur: props.onBlur,
    isActive: props.isActive
  });
};

StartButton.propTypes = commonButtonPropTypes$1;

var css$6 = ".ButtonIconLarge {\n  padding: 2px;\n  width: 48px;\n  min-width: 48px;\n  height: 38px;\n  display: inline-flex;\n  flex-direction: column;\n  align-items: center; }\n  .ButtonIconLarge__text {\n    margin-top: auto; }\n  .ButtonIconLarge .ButtonIconLarge__icon {\n    flex-grow: 1;\n    width: 20px;\n    height: 20px;\n    margin: 1px auto 2px; }\n  .ButtonIconLarge img {\n    max-width: 20px;\n    max-height: 20px;\n    display: block;\n    filter: grayscale(1);\n    position: relative;\n    top: 50%;\n    transform: translateY(-50%);\n    margin: 0 auto; }\n  .ButtonIconLarge:disabled, .ButtonIconLarge.disabled {\n    color: #808088; }\n    .ButtonIconLarge:disabled:hover, .ButtonIconLarge.disabled:hover {\n      box-shadow: none; }\n      .ButtonIconLarge:disabled:hover img, .ButtonIconLarge.disabled:hover img {\n        filter: grayscale(1); }\n  .ButtonIconLarge:hover {\n    box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #ffffff; }\n    .ButtonIconLarge:hover img {\n      filter: grayscale(0); }\n  .ButtonIconLarge:active:focus {\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #0c0c0c;\n    padding: 3px 1px 1px 3px; }\n  .ButtonIconLarge__icon {\n    flex-grow: 1;\n    width: 20px;\n    height: 20px;\n    margin: 1px auto 2px;\n    align-content: center; }\n";
styleInject(css$6);

var ButtonIconLarge = function ButtonIconLarge(props) {
  return React__default.createElement(AbstractButton, {
    className: cx('ButtonIconLarge', props.className),
    onClick: props.onClick,
    isDisabled: props.isDisabled
  }, React__default.createElement("div", {
    className: "ButtonIconLarge__icon"
  }, React__default.createElement("img", {
    src: props.icon
  })), React__default.createElement("div", {
    className: "ButtonIconLarge__text"
  }, props.title));
};

ButtonIconLarge.propTypes = _objectSpread({}, commonButtonPropTypes, {
  icon: propTypes.string,
  title: propTypes.string
});

var css$7 = ".btn.ButtonIconSmall {\n  height: 22px;\n  width: 22px;\n  padding: 0px; }\n  .btn.ButtonIconSmall img {\n    margin: 3px;\n    max-height: 16px;\n    max-width: 16px; }\n  .btn.ButtonIconSmall:hover {\n    box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px #ffffff; }\n  .btn.ButtonIconSmall:hover:focus:active, .btn.ButtonIconSmall:hover:active, .btn.ButtonIconSmall.active, .btn.ButtonIconSmall.clicked {\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #808088; }\n    .btn.ButtonIconSmall:hover:focus:active img, .btn.ButtonIconSmall:hover:active img, .btn.ButtonIconSmall.active img, .btn.ButtonIconSmall.clicked img {\n      margin: 4px 2px 2px 4px; }\n  .btn.ButtonIconSmall.btn--disabled img {\n    filter: grayscale(1); }\n";
styleInject(css$7);

var ButtonIconSmall = function ButtonIconSmall(props) {
  return React__default.createElement(AbstractButton, {
    className: cx('ButtonIconSmall', props.className),
    onClick: props.onClick,
    isDisabled: props.isDisabled,
    isActive: props.isActive,
    title: props.title
  }, React__default.createElement("img", {
    src: props.icon
  }));
};

ButtonIconSmall.propTypes = _objectSpread({}, commonButtonPropTypes$1, {
  icon: propTypes.string
});

var css$8 = ".Frame {\n  position: relative;\n  background-color: #bbc3c4;\n  padding: 3px;\n  box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #bbc3c4, inset -2px -2px 0px #808088, inset 2px 2px 0px #ffffff;\n  display: inline-block; }\n";
styleInject(css$8);

var WindowFrame = function WindowFrame(props) {
  return React__default.createElement("div", {
    className: cx('Frame', props.className),
    ref: props.innerRef
  }, props.children);
};

WindowFrame.propTypes = {
  children: propTypes.node,
  className: propTypes.string
};

var StandardMenuItem = function StandardMenuItem(props) {
  return React__default.createElement("div", {
    className: cx('StandardMenuItem', props.className, props.type, {
      'StandardMenuItem--has-options': props.options,
      active: props.isActive,
      'StandardMenuItem--radio-selected': props.isSelected,
      'StandardMenuItem--checked': props.isChecked
    }),
    onMouseEnter: props.mouseEnterItem,
    onTouchStart: props.mouseEnterItem
  }, React__default.createElement("button", {
    className: cx('StandardMenuItem__button', {
      disabled: props.isDisabled
    }),
    onClick: !props.options && !props.isDisabled ? props.closeOnClick(props.onClick) : undefined,
    style: props.icon ? {
      backgroundImage: "url('".concat(props.icon, "')")
    } : undefined,
    value: props.value
  }, props.title), props.options && React__default.createElement(props.StandardMenu, {
    className: "StandardMenuItem__child",
    options: props.options,
    value: props.value,
    mouseEnterItem: props.mouseEnterItem,
    closeOnClick: props.closeOnClick
  }));
};

StandardMenuItem.defaultProps = {
  onClick: function onClick() {},
  closeOnClick: function closeOnClick() {
    console.error('Menus require a closeOnClick prop to function correctly'); // eslint-disable-line
  },
  value: []
};
StandardMenuItem.propTypes = {
  className: propTypes.string,
  title: propTypes.string.isRequired,
  icon: propTypes.string,
  value: propTypes.arrayOf(propTypes.string),
  mouseEnterItem: propTypes.func,
  options: propTypes.any,
  isDisabled: propTypes.bool,
  isActive: propTypes.bool,
  onClick: propTypes.func,
  type: propTypes.string
};

var css$9 = ".StandardMenu {\n  display: inline-flex;\n  flex-direction: column;\n  word-wrap: none;\n  white-space: nowrap;\n  text-overflow: clip; }\n  .StandardMenu > div {\n    position: relative; }\n    .StandardMenu > div > button {\n      user-select: none;\n      position: relative;\n      display: block;\n      width: 100%;\n      padding: 0px 20px 0px 28px;\n      text-align: left;\n      background-repeat: no-repeat;\n      background-size: 16px;\n      background-position: 3px center;\n      background-color: rgba(0, 0, 0, 0);\n      border: none;\n      outline: none;\n      height: 20px; }\n      .StandardMenu > div > button:before {\n        content: \"\";\n        position: absolute;\n        left: 0px;\n        top: 0px;\n        height: 16px;\n        width: 16px;\n        background-repeat: no-repeat;\n        background-position: center; }\n      .StandardMenu > div > button .StandardMenu__item__text {\n        padding: 0px 20px 0px 0px; }\n      .StandardMenu > div > button:disabled, .StandardMenu > div > button.disabled {\n        color: #808088; }\n      .StandardMenu > div > button:not(:only-child):after {\n        content: \"\";\n        position: absolute;\n        background-image: url(\"data:image/gif;base64,R0lGODlhBAAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAEAAcAAAIIhA4maeyrlCgAOw==\");\n        top: 0px;\n        left: 0px;\n        height: 100%;\n        width: calc(100% - 8px);\n        background-position: right center;\n        background-repeat: no-repeat; }\n    .StandardMenu > div.radio-selected > button:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhBgAGAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAGAAYAAAIIFA6Gy816RAEAOw==\"); }\n    .StandardMenu > div.checked > button:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhBwAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAHAAcAAAIMlA9nwMj9xGuLIlUAADs=\"); }\n    .StandardMenu > div.checked.disabled > button:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhBwAHAJEAAAAAAP///5mZmf///yH5BAEAAAMALAAAAAAHAAcAAAIMnC9nwsj9xmuLIlUAADs=\"); }\n    .StandardMenu > div.active, .StandardMenu > div.clicked {\n      color: #ffffff; }\n      .StandardMenu > div.active > button:not(.disabled), .StandardMenu > div.clicked > button:not(.disabled) {\n        color: #ffffff;\n        background-color: #0000a2; }\n        .StandardMenu > div.active > button:not(.disabled):not(:only-child):after, .StandardMenu > div.clicked > button:not(.disabled):not(:only-child):after {\n          background-image: url(\"data:image/gif;base64,R0lGODlhBAAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAEAAcAAAIIjB4maeyrlCgAOw==\"); }\n    .StandardMenu > div > .window,\n    .StandardMenu > div > .Frame {\n      position: absolute;\n      visibility: hidden;\n      width: auto; }\n      @media (min-height: 720px) and (min-width: 960px) {\n        .StandardMenu > div > .window,\n        .StandardMenu > div > .Frame {\n          transition: max-width cubic-bezier(0.38, 0.01, 0, 1) 200ms, max-height cubic-bezier(0.38, 0.01, 0, 1) 200ms; } }\n    .StandardMenu > div.active > .window,\n    .StandardMenu > div.active > .Frame {\n      width: auto;\n      visibility: visible; }\n    .StandardMenu > div > .window,\n    .StandardMenu > div > .Frame {\n      left: calc(100% - 3px);\n      top: -3px;\n      max-width: 0%; }\n    .StandardMenu > div:hover > .window,\n    .StandardMenu > div:hover > .Frame, .StandardMenu > div.active > .window,\n    .StandardMenu > div.active > .Frame {\n      max-width: 400%; }\n  .StandardMenu > div:empty:not(:only-child) {\n    position: relative;\n    width: 95%;\n    margin: 2px auto;\n    border-top: 1px solid #808088;\n    border-bottom: 1px solid #ffffff;\n    display: none; }\n  .StandardMenu > div:not(:empty) + div:empty:not(:last-child):not(:first-child) {\n    display: block; }\n  .StandardMenu.css div__sub-menu--top > .window,\n  .StandardMenu.css div__sub-menu--top > .Frame {\n    position: absolute;\n    visibility: hidden;\n    width: auto; }\n    @media (min-height: 720px) and (min-width: 960px) {\n      .StandardMenu.css div__sub-menu--top > .window,\n      .StandardMenu.css div__sub-menu--top > .Frame {\n        transition: max-width cubic-bezier(0.38, 0.01, 0, 1) 200ms, max-height cubic-bezier(0.38, 0.01, 0, 1) 200ms; } }\n  .StandardMenu.css div__sub-menu--top.active > .window,\n  .StandardMenu.css div__sub-menu--top.active > .Frame {\n    width: auto;\n    visibility: visible; }\n  .StandardMenu.css div__sub-menu--top > .window,\n  .StandardMenu.css div__sub-menu--top > .Frame {\n    bottom: calc(100% + $windowPadding);\n    left: 0px;\n    height: 0px;\n    max-height: 0%;\n    max-width: 100%; }\n  .StandardMenu.css div__sub-menu--top:hover > .window,\n  .StandardMenu.css div__sub-menu--top:hover > .Frame, .StandardMenu.css div__sub-menu--top.active > .window,\n  .StandardMenu.css div__sub-menu--top.active > .Frame {\n    height: initial;\n    max-height: 100%; }\n  .StandardMenu.css div__sub-menu--bottom > .window,\n  .StandardMenu.css div__sub-menu--bottom > .Frame {\n    position: absolute;\n    visibility: hidden;\n    width: auto; }\n    @media (min-height: 720px) and (min-width: 960px) {\n      .StandardMenu.css div__sub-menu--bottom > .window,\n      .StandardMenu.css div__sub-menu--bottom > .Frame {\n        transition: max-width cubic-bezier(0.38, 0.01, 0, 1) 200ms, max-height cubic-bezier(0.38, 0.01, 0, 1) 200ms; } }\n  .StandardMenu.css div__sub-menu--bottom.active > .window,\n  .StandardMenu.css div__sub-menu--bottom.active > .Frame {\n    width: auto;\n    visibility: visible; }\n  .StandardMenu.css div__sub-menu--bottom > .window,\n  .StandardMenu.css div__sub-menu--bottom > .Frame {\n    top: calc(100% + $windowPadding);\n    left: 0px;\n    max-height: 0%;\n    max-width: 100%; }\n  .StandardMenu.css div__sub-menu--bottom:hover > .window,\n  .StandardMenu.css div__sub-menu--bottom:hover > .Frame, .StandardMenu.css div__sub-menu--bottom.active > .window,\n  .StandardMenu.css div__sub-menu--bottom.active > .Frame {\n    height: initial;\n    max-height: 100%; }\n  .StandardMenu.css div__sub-menu--left > .window,\n  .StandardMenu.css div__sub-menu--left > .Frame {\n    position: absolute;\n    visibility: hidden;\n    width: auto; }\n    @media (min-height: 720px) and (min-width: 960px) {\n      .StandardMenu.css div__sub-menu--left > .window,\n      .StandardMenu.css div__sub-menu--left > .Frame {\n        transition: max-width cubic-bezier(0.38, 0.01, 0, 1) 200ms, max-height cubic-bezier(0.38, 0.01, 0, 1) 200ms; } }\n  .StandardMenu.css div__sub-menu--left.active > .window,\n  .StandardMenu.css div__sub-menu--left.active > .Frame {\n    width: auto;\n    visibility: visible; }\n  .StandardMenu.css div__sub-menu--left > .window,\n  .StandardMenu.css div__sub-menu--left > .Frame {\n    left: -100%;\n    top: -3px;\n    max-width: 0%; }\n  .StandardMenu.css div__sub-menu--left:hover > .window,\n  .StandardMenu.css div__sub-menu--left:hover > .Frame, .StandardMenu.css div__sub-menu--left.active > .window,\n  .StandardMenu.css div__sub-menu--left.active > .Frame {\n    max-width: 100%; }\n  .StandardMenu.css div:active,\n  .StandardMenu.css div .active {\n    display: none; }\n  .StandardMenu.css div:hover > .window,\n  .StandardMenu.css div:hover > .Frame {\n    width: auto;\n    visibility: visible;\n    display: block; }\n  .StandardMenu.css div:hover > button {\n    background-color: #0000a2;\n    color: #ffffff; }\n    .StandardMenu.css div:hover > button:after {\n      background-image: url(\"data:image/gif;base64,R0lGODlhBAAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAEAAcAAAIIjB4maeyrlCgAOw==\"); }\n\n.StandardMenuItem--empty .StandardMenuItem__button {\n  text-shadow: 1px 1px #ffffff;\n  text-align: center; }\n";
styleInject(css$9);

var DIVIDER = 'divider';
var flattenWithDividers = function flattenWithDividers(options) {
  return options.reduce(function (acc, val, idx) {
    if (!Array.isArray(val)) {
      acc.push(val);
    } else {
      acc = acc.concat(["".concat(DIVIDER, "--group-").concat(idx, "-start")].concat(_toConsumableArray(val), ["".concat(DIVIDER, "--group-").concat(idx, "-end")]));
    }

    return acc;
  }, []);
};

var StandardMenu = function StandardMenu(props) {
  var options = flattenWithDividers(props.options);
  var hasOptions = Array.isArray(options);
  return React__default.createElement(WindowFrame, {
    className: cx('StandardMenu', props.className, props.direction, {
      'StandardMenu--visible': props.isVisible
    })
  }, hasOptions && options.length > 0 ? options.map(function (option) {
    if (typeof option === 'string' && option.includes(DIVIDER)) {
      return React__default.createElement("div", {
        key: option.toString(),
        className: "".concat(DIVIDER, " ").concat(option)
      });
    }

    return React__default.createElement(StandardMenuItem, _extends$1({
      key: "StandardMenu-item-".concat(option.title)
    }, option, {
      value: [].concat(_toConsumableArray(props.value), [option.title]),
      closeOnClick: props.closeOnClick,
      mouseEnterItem: props.mouseEnterItem,
      StandardMenu: StandardMenu
    }));
  }) : React__default.createElement(StandardMenuItem, {
    title: "(Empty)",
    className: 'StandardMenuItem--empty',
    mouseEnterItem: props.mouseEnterItem,
    closeOnClick: props.closeOnClick,
    StandardMenu: StandardMenu,
    isDisabled: true
  }));
};

StandardMenu.defaultProps = {
  value: []
};
var standardMenuProps = {
  value: propTypes.arrayOf(propTypes.string),
  mouseEnterItem: propTypes.func,
  className: propTypes.string,
  direction: propTypes.oneOf(['up', 'down', 'left', 'right']),
  options: propTypes.any,
  isVisible: propTypes.bool
};
StandardMenu.propTypes = standardMenuProps;

var standardMenuProps$1 = StandardMenu.propTypes;

var AbstractIcon =
/*#__PURE__*/
function (_Component) {
  _inherits(AbstractIcon, _Component);

  function AbstractIcon() {
    var _getPrototypeOf2;

    var _this;

    _classCallCheck(this, AbstractIcon);

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(AbstractIcon)).call.apply(_getPrototypeOf2, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this), "state", {
      doubleReady: false
    });

    _defineProperty(_assertThisInitialized(_this), "disableAction", function () {
      _this.setState({
        doubleReady: false
      });
    });

    _defineProperty(_assertThisInitialized(_this), "checkDoubleClick", function () {
      _this.handleClick();

      if (!_this.props.onDoubleClick) {
        return;
      }

      if (_this.state.doubleReady) {
        _this.props.onDoubleClick();

        _this.disableAction();
      } else {
        _this.setState({
          doubleReady: true
        });

        setTimeout(_this.disableAction, 700);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleClick", function () {
      _this.icon.focus();

      if (_this.props.onClick) {
        _this.props.onClick();
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleContextMenu", function (e) {
      e.preventDefault();

      _this.icon.focus();

      if (_this.props.onContextMenu) {
        _this.props.onContextMenu(e);
      } //return false;

    });

    return _this;
  }

  _createClass(AbstractIcon, [{
    key: "render",
    value: function render() {
      var _this2 = this;

      var props = this.props;
      var Comp = props.href ? 'a' : 'button';
      var iconProps = {
        onClick: this.checkDoubleClick,
        onContextMenu: this.props.onContextMenu && this.handleContextMenu,
        onTouchEnd: this.props.onDoubleClick || this.props.onClick,
        className: cx('icon', props.className),
        title: props.alt,
        value: props.value,
        ref: function ref(icon) {
          _this2.icon = icon;
        },
        href: props.href
      };
      var contents = React__default.createElement(React__default.Fragment, null, React__default.createElement("div", {
        className: "icon__icon",
        style: {
          backgroundImage: "url('".concat(props.icon, "')")
        }
      }), React__default.createElement("div", {
        className: "icon__text"
      }, props.title));

      if (this.props.onClick || this.props.onDoubleClick) {
        return React__default.createElement(Comp, _extends$1({
          ref: function ref(icon) {
            _this2.icon = icon;
          }
        }, iconProps), contents);
      }

      return React__default.createElement("div", iconProps, contents);
    }
  }]);

  return AbstractIcon;
}(React.Component);

var iconProps = {
  title: propTypes.string,
  icon: propTypes.string,
  children: propTypes.node,
  className: propTypes.string,
  alt: propTypes.string,
  value: propTypes.any,
  onClick: propTypes.func,
  onDoubleClick: propTypes.func,
  onContextMenu: propTypes.func,
  href: propTypes.string
};
AbstractIcon.propTypes = iconProps;

var iconProps$1 = AbstractIcon.propTypes;

var css$a = ".icon.ExplorerIcon {\n  position: relative;\n  display: block;\n  outline: none;\n  background: none;\n  border: none;\n  color: initial;\n  text-decoration: none;\n  padding: 1px 7px 2px;\n  padding: initial;\n  margin: 3px;\n  width: 52px;\n  height: 58px;\n  text-align: center;\n  display: flex;\n  flex-direction: column;\n  align-items: center; }\n  .icon.ExplorerIcon .icon__icon {\n    display: block;\n    background-size: contain;\n    background-position: center;\n    background-repeat: no-repeat; }\n  .icon.ExplorerIcon:focus, .icon.ExplorerIcon:active, .icon.ExplorerIcon:active:focus, .icon.ExplorerIcon.is-active {\n    outline: none; }\n    .icon.ExplorerIcon:focus .icon__icon, .icon.ExplorerIcon:active .icon__icon, .icon.ExplorerIcon:active:focus .icon__icon, .icon.ExplorerIcon.is-active .icon__icon {\n      filter: hue-rotate(70deg) contrast(0.3) saturate(2); }\n    .icon.ExplorerIcon:focus .icon__text, .icon.ExplorerIcon:active .icon__text, .icon.ExplorerIcon:active:focus .icon__text, .icon.ExplorerIcon.is-active .icon__text {\n      background-color: #0000a2;\n      color: #ffffff;\n      outline: 1px dotted #ffffff;\n      outline-offset: -1px; }\n  .icon.ExplorerIcon .icon__icon {\n    width: 32px;\n    height: 32px;\n    margin: 0 3px; }\n  .icon.ExplorerIcon .icon__text {\n    margin: 2px;\n    position: absolute;\n    top: 34px;\n    padding: 2px;\n    max-height: 22px;\n    max-width: 100%;\n    overflow: hidden;\n    display: inline-block; }\n  .icon.ExplorerIcon:focus .icon__text, .icon.ExplorerIcon:active .icon__text, .icon.ExplorerIcon:active:focus .icon__text, .icon.ExplorerIcon.active .icon__text, .icon.ExplorerIcon.clicked .icon__text {\n    padding: 2px 3px;\n    max-height: initial;\n    z-index: 1; }\n";
styleInject(css$a);

var ExplorerIcon = function ExplorerIcon(props) {
  return React__default.createElement(AbstractIcon, {
    onClick: props.onClick,
    onDoubleClick: props.onDoubleClick,
    onContextMenu: props.onContextMenu,
    alt: props.alt,
    className: cx('ExplorerIcon', props.className),
    icon: props.icon,
    title: props.title,
    href: props.href
  });
};

ExplorerIcon.propTypes = iconProps$1;

var css$b = ".icon.ListIcon {\n  position: relative;\n  display: block;\n  outline: none;\n  background: none;\n  border: none;\n  color: initial;\n  text-decoration: none;\n  padding: 1px 7px 2px;\n  height: 18px;\n  margin: 2px;\n  text-align: left;\n  display: flex;\n  align-items: center; }\n  .icon.ListIcon .icon__icon {\n    display: block;\n    background-size: contain;\n    background-position: center;\n    background-repeat: no-repeat; }\n  .icon.ListIcon:focus, .icon.ListIcon:active, .icon.ListIcon:active:focus, .icon.ListIcon.is-active {\n    outline: none; }\n    .icon.ListIcon:focus .icon__icon, .icon.ListIcon:active .icon__icon, .icon.ListIcon:active:focus .icon__icon, .icon.ListIcon.is-active .icon__icon {\n      filter: hue-rotate(70deg) contrast(0.3) saturate(2); }\n    .icon.ListIcon:focus .icon__text, .icon.ListIcon:active .icon__text, .icon.ListIcon:active:focus .icon__text, .icon.ListIcon.is-active .icon__text {\n      background-color: #0000a2;\n      color: #ffffff;\n      outline: 1px dotted #ffffff;\n      outline-offset: -1px; }\n  .icon.ListIcon .icon__icon {\n    display: inline-block;\n    width: 16px;\n    height: 16px;\n    margin-right: 2px; }\n  .icon.ListIcon .icon__text {\n    position: relative;\n    padding: 2px;\n    display: inline-block;\n    overflow: hidden;\n    white-space: nowrap;\n    text-overflow: ellipsis;\n    width: calc(100% - 20px);\n    padding-bottom: 3px; }\n  .icon.ListIcon:focus .icon__text, .icon.ListIcon:active .icon__text, .icon.ListIcon:active:focus .icon__text, .icon.ListIcon.active .icon__text, .icon.ListIcon.clicked .icon__text {\n    max-height: initial; }\n";
styleInject(css$b);

var css$c = ".ExplorerView {\n  display: flex;\n  flex-flow: column wrap;\n  height: 100%;\n  width: 100%;\n  align-content: flex-start; }\n  .ExplorerView--fixed-width {\n    overflow-y: scroll;\n    height: initial; }\n  .ExplorerView--fixed-height {\n    overflow-x: scroll;\n    width: initial; }\n";
styleInject(css$c);

var ExplorerView = function ExplorerView(props) {
  return React__default.createElement("div", {
    className: cx('ExplorerView', props.className, {
      'ExplorerView--fixed-width': props.fixedWidth,
      'ExplorerView--fixed-height': props.fixedHeight
    }),
    style: {
      backgroundColor: props.style.backgroundColor,
      backgroundImage: props.style.backgroundImage,
      backgroundSize: props.style.backgroundSize,
      backgroundRepeat: props.style.backgroundRepeat,
      backgroundPosition: props.style.backgroundPosition
    }
  }, props.children);
};

ExplorerView.defaultProps = {
  style: {}
};
ExplorerView.propTypes = {
  children: propTypes.node,
  fixedHeight: propTypes.bool,
  fixedWidth: propTypes.bool,
  className: propTypes.string
};

var Toggle = function Toggle(props) {
  return React__default.createElement("div", {
    className: cx('Toggle', props.className)
  }, React__default.createElement("input", {
    type: props.type,
    id: props.id,
    disabled: props.isDisabled,
    value: props.value,
    checked: props.checked,
    onChange: props.onChange,
    name: props.name
  }), React__default.createElement("label", {
    htmlFor: props.id
  }, React__default.createElement("span", null, props.label)));
};

var toggleProps = {
  label: propTypes.string,
  type: propTypes.string,
  id: propTypes.string,
  name: propTypes.string,
  checked: propTypes.bool,
  onChange: propTypes.func,
  isDisabled: propTypes.bool
};
Toggle.propTypes = toggleProps;

var css$d = ".Checkbox {\n  display: inline-block; }\n  .Checkbox input[type=\"checkbox\"] {\n    opacity: 0;\n    display: none;\n    cursor: pointer; }\n    .Checkbox input[type=\"checkbox\"] + label {\n      position: relative;\n      padding: 1px 0px;\n      padding-left: 16px; }\n      .Checkbox input[type=\"checkbox\"] + label > span,\n      .Checkbox input[type=\"checkbox\"] + label > div {\n        display: inline-block;\n        border: 1px solid rgba(0, 0, 0, 0); }\n      .Checkbox input[type=\"checkbox\"] + label:before {\n        content: \"\";\n        position: absolute;\n        left: 0px;\n        top: 1px;\n        width: 20px;\n        height: 12px;\n        background-repeat: no-repeat; }\n    .Checkbox input[type=\"checkbox\"]:checked + label {\n      border-bottom-left-radius: 2px;\n      border-bottom-right-radius: 2px; }\n    .Checkbox input[type=\"checkbox\"]:checked:active + label > span,\n    .Checkbox input[type=\"checkbox\"]:checked:active + label > div, .Checkbox input[type=\"checkbox\"]:checked:focus + label > span,\n    .Checkbox input[type=\"checkbox\"]:checked:focus + label > div, .Checkbox input[type=\"checkbox\"]:checked:active:focus + label > span,\n    .Checkbox input[type=\"checkbox\"]:checked:active:focus + label > div, .Checkbox input[type=\"checkbox\"]:checked.active + label > span,\n    .Checkbox input[type=\"checkbox\"]:checked.active + label > div, .Checkbox input[type=\"checkbox\"]:checked.clicked + label > span,\n    .Checkbox input[type=\"checkbox\"]:checked.clicked + label > div {\n      border: 1px dotted #0c0c0c; }\n    .Checkbox input[type=\"checkbox\"]:disabled + label, .Checkbox input[type=\"checkbox\"].disabled + label {\n      color: #808088; }\n    .Checkbox input[type=\"checkbox\"] + label:before {\n      width: 13px;\n      height: 13px;\n      background-color: #ffffff;\n      box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c; }\n    .Checkbox input[type=\"checkbox\"]:checked + label:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhBwAHAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAHAAcAAAIMlA9nwMj9xGuLIlUAADs=\");\n      background-position: center;\n      background-size: 8px; }\n    .Checkbox input[type=\"checkbox\"]:disabled + label:before, .Checkbox input[type=\"checkbox\"].disabled + label:before {\n      background-color: #bbc3c4; }\n    .Checkbox input[type=\"checkbox\"]:disabled:checked + label:before, .Checkbox input[type=\"checkbox\"].disabled:checked + label:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhBwAHAJEAAAAAAP///5mZmf///yH5BAEAAAMALAAAAAAHAAcAAAIMnC9nwsj9xmuLIlUAADs=\"); }\n";
styleInject(css$d);

var Checkbox = function Checkbox(props) {
  return React__default.createElement(Toggle, _extends$1({}, props, {
    className: cx('Checkbox', props.className),
    type: "checkbox"
  }));
};

Checkbox.propTypes = Toggle.propTypes;

var css$e = ".Radio {\n  display: inline-block; }\n  .Radio input[type=\"radio\"] {\n    opacity: 0;\n    display: none;\n    cursor: pointer; }\n    .Radio input[type=\"radio\"] + label {\n      position: relative;\n      padding: 1px 0px;\n      padding-left: 16px; }\n      .Radio input[type=\"radio\"] + label > span,\n      .Radio input[type=\"radio\"] + label > div {\n        display: inline-block;\n        border: 1px solid rgba(0, 0, 0, 0); }\n      .Radio input[type=\"radio\"] + label:before {\n        content: \"\";\n        position: absolute;\n        left: 0px;\n        top: 1px;\n        width: 20px;\n        height: 12px;\n        background-repeat: no-repeat; }\n    .Radio input[type=\"radio\"]:checked + label {\n      border-bottom-left-radius: 2px;\n      border-bottom-right-radius: 2px; }\n    .Radio input[type=\"radio\"]:checked:active + label > span,\n    .Radio input[type=\"radio\"]:checked:active + label > div, .Radio input[type=\"radio\"]:checked:focus + label > span,\n    .Radio input[type=\"radio\"]:checked:focus + label > div, .Radio input[type=\"radio\"]:checked:active:focus + label > span,\n    .Radio input[type=\"radio\"]:checked:active:focus + label > div, .Radio input[type=\"radio\"]:checked.active + label > span,\n    .Radio input[type=\"radio\"]:checked.active + label > div, .Radio input[type=\"radio\"]:checked.clicked + label > span,\n    .Radio input[type=\"radio\"]:checked.clicked + label > div {\n      border: 1px dotted #0c0c0c; }\n    .Radio input[type=\"radio\"]:disabled + label, .Radio input[type=\"radio\"].disabled + label {\n      color: #808088; }\n    .Radio input[type=\"radio\"] + label:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhDAAMAKIAAAAAAP///8zMzJmZmf///wAAAAAAAAAAACH5BAEAAAQALAAAAAAMAAwAAAMqSErTs6uBCVqcIQesBtCaEDAfGAaeeaZqILKqyLQyI4hhTWT3nUEKECQBADs=\"); }\n    .Radio input[type=\"radio\"]:checked + label:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhDAAMAKIAAAAAAP///8zMzJmZmf///wAAAAAAAAAAACH5BAEAAAQALAAAAAAMAAwAAAMtSErTs6uBCVqcIQesBtCaEDBfhmWiZ1JooG5skJZwOA6g3QliKC4oXg+iAEESADs=\"); }\n    .Radio input[type=\"radio\"]:disabled + label:before, .Radio input[type=\"radio\"].disabled + label:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhDAAMAKIAAAAAAP///8zMzJmZmf///wAAAAAAAAAAACH5BAEAAAQALAAAAAAMAAwAAAMpSErTs6uBCVqccAY1AFTC1n1LOJKE6aEqmorsxggCRMtEENA3vug6SAIAOw==\"); }\n    .Radio input[type=\"radio\"]:disabled:checked + label:before, .Radio input[type=\"radio\"].disabled:checked + label:before {\n      background-image: url(\"data:image/gif;base64,R0lGODlhDAAMAKIAAAAAAP///8zMzJmZmf///wAAAAAAAAAAACH5BAEAAAQALAAAAAAMAAwAAAMtSErTs6uBCVqccAY1AFTC1i0YGIwE5REhqppourLiZ3KCAOWbEgQ5Xg/y+0ESADs=\"); }\n";
styleInject(css$e);

var Radio = function Radio(props) {
  return React__default.createElement(Toggle, _extends$1({}, props, {
    className: "Radio",
    type: "radio"
  }));
};

Radio.propTypes = Toggle.propTypes;

var css$f = ".InputText {\n  position: relative;\n  padding: 3px 3px 6px;\n  font-size: 11px;\n  border: none;\n  box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c; }\n  .InputText:active, .InputText:focus, .InputText:active:focus, .InputText.clicked {\n    outline: none; }\n  .InputText:disabled, .InputText.disabled {\n    background-color: #bbc3c4; }\n";
styleInject(css$f);

var InputText =
/*#__PURE__*/
function (_Component) {
  _inherits(InputText, _Component);

  function InputText() {
    var _getPrototypeOf2;

    var _this;

    _classCallCheck(this, InputText);

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(InputText)).call.apply(_getPrototypeOf2, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this), "state", {
      value: _this.props.initialValue
    });

    _defineProperty(_assertThisInitialized(_this), "handleChange", function (e) {
      if (_this.props.initialValue) {
        _this.setState({
          value: e.target.value
        });
      }

      _this.props.onChange(e.target.value);
    });

    _defineProperty(_assertThisInitialized(_this), "handleBlur", function () {
      _this.props.onBlur(_this.state.value);
    });

    return _this;
  }

  _createClass(InputText, [{
    key: "render",
    value: function render() {
      return React__default.createElement("input", {
        type: "text",
        className: cx('InputText text', this.props.className),
        value: this.props.initialValue ? this.state.value : this.props.value,
        id: this.props.id,
        disabled: this.props.isDisabled,
        name: this.props.name || this.props.id,
        onBlur: this.handleBlur,
        onChange: this.handleChange,
        onKeyDown: this.props.onKeyDown,
        onFocus: this.props.onFocus
      });
    }
  }]);

  return InputText;
}(React.Component);

_defineProperty(InputText, "defaultProps", {
  onChange: function onChange() {},
  onKeyDown: function onKeyDown() {},
  onBlur: function onBlur() {},
  onFocus: function onFocus() {}
});

InputText.propTypes = {
  className: propTypes.string,
  value: propTypes.string,
  initialValue: propTypes.string,
  isDisabled: propTypes.bool,
  id: propTypes.string,
  name: propTypes.string,
  onBlur: propTypes.func.isRequired,
  onChange: propTypes.func.isRequired,
  onFocus: propTypes.func.isRequired,
  onKeyDown: propTypes.func.isRequired
};

var css$g = ".w98 {\n  /* stylelint-disable */ }\n  .w98 .Select {\n    position: relative; }\n    .w98 .Select .Select-control {\n      width: 100%; }\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-input,\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-placeholder,\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-value {\n        width: calc(100% - 4px); }\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-input {\n        display: none !important; }\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-value,\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-placeholder {\n        height: 16px;\n        background-color: #ffffff;\n        border: none;\n        box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c;\n        padding: 2px; }\n        .w98 .Select .Select-control .Select-multi-value-wrapper .Select-value .Select-value-label > div,\n        .w98 .Select .Select-control .Select-multi-value-wrapper .Select-placeholder .Select-value-label > div {\n          margin: 1px;\n          margin-right: 17px;\n          padding-left: 1px;\n          outline: 1px dotted rgba(0, 0, 0, 0); }\n        .w98 .Select .Select-control .Select-multi-value-wrapper .Select-value:active .Select-value-label > div, .w98 .Select .Select-control .Select-multi-value-wrapper .Select-value:focus .Select-value-label > div,\n        .w98 .Select .Select-control .Select-multi-value-wrapper .Select-placeholder:active .Select-value-label > div,\n        .w98 .Select .Select-control .Select-multi-value-wrapper .Select-placeholder:focus .Select-value-label > div {\n          outline: 1px dotted #ffffff;\n          outline-offset: -1px;\n          background-color: #0000a2;\n          color: #ffffff; }\n      .w98 .Select .Select-control .Select-multi-value-wrapper .Select-placeholder {\n        display: flex;\n        align-items: center;\n        padding: 2px 0px 2px 4px; }\n      .w98 .Select .Select-control .Select-arrow-zone {\n        position: absolute;\n        box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #bbc3c4, inset -2px -2px 0px #808088, inset 2px 2px 0px #ffffff;\n        height: 16px;\n        width: 16px;\n        left: calc(100% - 18px);\n        top: 2px;\n        background-color: #bbc3c4;\n        background-repeat: no-repeat;\n        background-position: center;\n        background-image: url(\"data:image/gif;base64,R0lGODlhBwAEAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAHAAQAAAIIhA+CKWoNmSgAOw==\"); }\n      .w98 .Select .Select-control .Select-clear-zone {\n        display: none; }\n    .w98 .Select .Select-menu-outer {\n      border: 1px solid #0c0c0c;\n      background-color: #ffffff; }\n      .w98 .Select .Select-menu-outer .Select-menu .Select-option {\n        padding: 1px; }\n        .w98 .Select .Select-menu-outer .Select-menu .Select-option:hover {\n          outline: 1px dotted #ffffff;\n          outline-offset: -1px;\n          background-color: #0000a2;\n          color: #ffffff; }\n    .w98 .Select.is-disabled {\n      pointer-events: none; }\n      .w98 .Select.is-disabled .Select-control .Select-multi-value-wrapper .Select-value,\n      .w98 .Select.is-disabled .Select-control .Select-multi-value-wrapper .Select-placeholder {\n        background-color: #bbc3c4; }\n      .w98 .Select.is-disabled .Select-control .Select-arrow-zone:after {\n        background-image: url(\"data:image/gif;base64,R0lGODlhCAAFAJEAAAAAAP///5mZmf///yH5BAEAAAMALAAAAAAIAAUAAAIMlC8zKBF6nIJyqqcKADs=\"); }\n";
styleInject(css$g);

var DefaultOptionComponent = function DefaultOptionComponent(props) {
  return React__default.createElement("div", props);
}; // copied straight from react select demos with slight changes


var menuRenderer$1 = function menuRenderer$$1(_ref) {
  var focusedOption = _ref.focusedOption,
      focusOption = _ref.focusOption,
      inputValue = _ref.inputValue,
      instancePrefix = _ref.instancePrefix,
      onFocus = _ref.onFocus,
      onOptionRef = _ref.onOptionRef,
      onSelect = _ref.onSelect,
      optionClassName = _ref.optionClassName,
      optionComponent = _ref.optionComponent,
      options = _ref.options,
      removeValue = _ref.removeValue,
      selectValue = _ref.selectValue,
      valueArray = _ref.valueArray,
      valueKey = _ref.valueKey;
  var Option$$1 = optionComponent || DefaultOptionComponent;
  return options.map(function (option, i) {
    var isSelected = valueArray && valueArray.some(function (x) {
      return x[valueKey] === option[valueKey];
    });
    var isFocused = option === focusedOption;
    var optionClass = cx(optionClassName, {
      'Select-option': true,
      'Select-option--icon': true,
      'is-selected': isSelected,
      'is-focused': isFocused,
      'is-disabled': option.disabled
    });
    return React__default.createElement(Option$$1, {
      className: optionClass,
      focusOption: focusOption,
      inputValue: inputValue,
      instancePrefix: instancePrefix,
      isDisabled: option.disabled,
      isFocused: isFocused,
      isSelected: isSelected,
      key: "option-".concat(i, "-").concat(option[valueKey]),
      onFocus: onFocus,
      onSelect: onSelect,
      option: option,
      optionIndex: i,
      ref: function ref(_ref2) {
        onOptionRef(_ref2, isFocused);
      },
      removeValue: removeValue,
      selectValue: selectValue,
      backgroundImage: option.icon
    }, React__default.createElement("span", null, option.label));
  });
};
menuRenderer$1.propTypes = {
  focusedOption: propTypes.object,
  inputValue: propTypes.string,
  instancePrefix: propTypes.string,
  optionClassName: propTypes.string,
  options: propTypes.array,
  valueArray: propTypes.array,
  valueKey: propTypes.string,
  focusOption: propTypes.func,
  onFocus: propTypes.func,
  onOptionRef: propTypes.func,
  onSelect: propTypes.func,
  optionComponent: propTypes.func,
  optionRenderer: propTypes.func,
  removeValue: propTypes.func,
  selectValue: propTypes.func
};

var ValueRenderer = function ValueRenderer(props) {
  return React__default.createElement("div", {
    style: {
      backgroundImage: props.icon ? "url('".concat(props.icon, "')") : 'none'
    }
  }, props.label);
};

ValueRenderer.propTypes = {
  icon: propTypes.string,
  label: propTypes.string
};

var Select =
/*#__PURE__*/
function (_Component) {
  _inherits(Select, _Component);

  function Select(props) {
    var _this;

    _classCallCheck(this, Select);

    _this = _possibleConstructorReturn(this, _getPrototypeOf(Select).call(this, props));

    _defineProperty(_assertThisInitialized(_this), "handleChange", function (e) {
      if (_this.props.onChange) {
        _this.setState({
          value: e.value
        });
      } else {
        _this.props.onChange(e);
      }
    });

    _this.state = {
      value: _this.props.onChange ? null : _this.props.value
    };
    return _this;
  }

  _createClass(Select, [{
    key: "render",
    value: function render() {
      var props = this.props;
      return React__default.createElement(Select$1, _extends$1({}, props, {
        className: "Select",
        placeholder: props.placeholder,
        onChange: this.handleChange,
        disabled: props.isDisabled,
        searchable: props.searchable,
        menuRenderer: props.useIcons ? menuRenderer$1 : undefined,
        valueRenderer: ValueRenderer,
        value: this.props.onChange ? this.props.value : this.state.value
      }));
    }
  }]);

  return Select;
}(React.Component);

_defineProperty(Select, "defaultProps", {
  placeholder: '',
  searchable: false
});

Select.propTypes = {
  placeholder: propTypes.any,
  isDisabled: propTypes.bool,
  searchable: propTypes.bool,
  useIcons: propTypes.bool
};

var css$h = ".FakeSelect {\n  position: relative;\n  display: flex;\n  height: 22px;\n  align-self: center;\n  align-items: center;\n  background-color: #ffffff;\n  overflow: hidden;\n  box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c; }\n  .FakeSelect__icon {\n    margin-left: 6px;\n    height: 16px; }\n  .FakeSelect__children {\n    margin-left: 6px;\n    margin-right: 28px;\n    white-space: nowrap;\n    overflow: hidden;\n    text-overflow: ellipsis; }\n  .FakeSelect__arrow {\n    position: absolute;\n    box-shadow: inset -1px -1px 0px #0c0c0c, inset 1px 1px 0px #bbc3c4, inset -2px -2px 0px #808088, inset 2px 2px 0px #ffffff;\n    height: 18px;\n    width: 18px;\n    left: calc(100% - 20px);\n    top: 2px;\n    background-color: #bbc3c4;\n    background-repeat: no-repeat;\n    background-position: center;\n    background-image: url(\"data:image/gif;base64,R0lGODlhBwAEAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAHAAQAAAIIhA+CKWoNmSgAOw==\"); }\n";
styleInject(css$h);

var FakeSelect = function FakeSelect(props) {
  return React__default.createElement("div", {
    className: cx('FakeSelect', {
      disabled: props.isDisabled
    })
  }, props.icon && React__default.createElement("img", {
    className: "FakeSelect__icon",
    src: props.icon
  }), React__default.createElement("div", {
    className: "FakeSelect__children"
  }, props.title), React__default.createElement("div", {
    className: "FakeSelect__arrow"
  }));
};

var css$i = ".SelectBox {\n  position: relative;\n  width: 100%;\n  background-color: #ffffff;\n  padding: 2px; }\n  .SelectBox:disabled, .SelectBox.disabled {\n    pointer-events: none;\n    background-color: #bbc3c4; }\n    .SelectBox:disabled > div, .SelectBox.disabled > div {\n      overflow: hidden; }\n    .SelectBox:disabled button, .SelectBox.disabled button {\n      color: #808088 !important; }\n    .SelectBox:disabled .icon, .SelectBox.disabled .icon {\n      filter: grayscale(1); }\n  .SelectBox > div {\n    position: relative;\n    overflow: auto; }\n  .SelectBox:after {\n    position: absolute;\n    top: 0px;\n    left: 0px;\n    width: 100%;\n    height: 100%;\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c;\n    pointer-events: none;\n    content: \"\"; }\n  .SelectBox button:not(.icon) {\n    display: block;\n    outline: none;\n    background: transparent;\n    border: none;\n    white-space: nowrap;\n    overflow: hidden;\n    color: #0c0c0c;\n    width: 100%;\n    text-align: left; }\n    .SelectBox button:not(.icon):after {\n      content: attr(title);\n      position: initial; }\n    .SelectBox button:not(.icon).is-active {\n      background-color: #0000a2;\n      color: #ffffff;\n      outline-offset: -1px;\n      outline: 1px dotted #ffffff; }\n  .SelectBox--ExplorerIcon > div {\n    display: flex;\n    flex-direction: row;\n    overflow-y: hidden;\n    padding-bottom: 20px; }\n    .SelectBox--ExplorerIcon > div .explorer-icon {\n      margin: 2px 8px; }\n  .SelectBox .icon--list {\n    margin: 0px;\n    padding: 1px; }\n    .SelectBox .icon--list .icon__text {\n      width: initial; }\n    .SelectBox .icon--list:focus:not(.is-active) .icon__text, .SelectBox .icon--list:active:not(.is-active) .icon__text {\n      background-color: transparent;\n      color: #0c0c0c;\n      outline: none;\n      outline-offset: -1px; }\n";
styleInject(css$i);

var isSelected = function isSelected(selected, val) {
  return Array.isArray(selected) ? selected.some(function (selectedEntry) {
    return selectedEntry === val;
  }) : selected === val;
};

var SelectBox = function SelectBox(props) {
  var Comp = props.component ? props.component : 'button';
  return React__default.createElement("div", {
    className: cx('SelectBox', props.component ? "SelectBox--".concat(props.component.name) : 'SelectBox--simple', {
      disabled: props.isDisabled
    })
  }, React__default.createElement("div", null, props.options.map(function (option) {
    return React__default.createElement(Comp, {
      key: _typeof$1(option.value) !== 'object' ? option.value : JSON.stringify(option.value),
      onClick: function onClick() {
        return props.onClick(option.value);
      },
      alt: props.component ? option.alt : undefined,
      className: cx(option.className, {
        'is-active': isSelected(props.selected, option.value)
      }),
      icon: props.component ? option.icon : undefined,
      title: option.title || (typeof option.value === 'string' ? option.value : ''),
      value: option.value
    });
  })));
};

SelectBox.propTypes = {
  component: propTypes.func,
  className: propTypes.string,
  title: propTypes.string,
  selected: propTypes.oneOfType([propTypes.string, propTypes.array]),
  isDisabled: propTypes.bool,
  options: propTypes.arrayOf(propTypes.shape({
    value: propTypes.any,
    title: propTypes.string,
    icon: propTypes.string,
    alt: propTypes.string,
    className: propTypes.string
  }))
};

var css$j = ".SelectMultipleSimple select[multiple] {\n  position: relative;\n  border: none;\n  background-color: #ffffff;\n  border-radius: 0px;\n  outline: none;\n  padding: 2px;\n  box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c; }\n  .SelectMultipleSimple select[multiple]:active, .SelectMultipleSimple select[multiple]:focus, .SelectMultipleSimple select[multiple]:active:focus, .SelectMultipleSimple select[multiple].active, .SelectMultipleSimple select[multiple].clicked {\n    outline: none; }\n  .SelectMultipleSimple select[multiple] option:active, .SelectMultipleSimple select[multiple] option:focus, .SelectMultipleSimple select[multiple] option:checked, .SelectMultipleSimple select[multiple] option.checked {\n    outline: 1px dotted #ffffff;\n    outline-offset: -1px;\n    background-color: #0000a2;\n    color: #ffffff; }\n";
styleInject(css$j);

var SelectMultipleSimple =
/*#__PURE__*/
function (_Component) {
  _inherits(SelectMultipleSimple, _Component);

  function SelectMultipleSimple(props) {
    var _this;

    _classCallCheck(this, SelectMultipleSimple);

    _this = _possibleConstructorReturn(this, _getPrototypeOf(SelectMultipleSimple).call(this, props));

    _defineProperty(_assertThisInitialized(_this), "updateValue", function (value) {
      _this.setState({
        value: value
      });

      _this.props.onChange(value);
    });

    _defineProperty(_assertThisInitialized(_this), "handleChange", function (event) {
      if (_this.props.multiple) {
        var selectedIndex = _this.state.value.findIndex(function (val) {
          return val === event.target.value;
        });

        var isSelected = selectedIndex !== -1;

        if (!isSelected && _this.props.selectMultiple) {
          _this.updateValue([].concat(_toConsumableArray(_this.state.value), [event.target.value]));

          return;
        }

        if (!isSelected) {
          _this.updateValue([event.target.value]);

          return;
        }

        if (isSelected) {
          _this.updateValue([].concat(_toConsumableArray(_this.state.value.slice(0, selectedIndex)), _toConsumableArray(_this.state.value.slice(selectedIndex + 1))));

          return;
        }
      } else {
        _this.updateValue(event.target.value);
      }
    });

    _this.state = {
      value: _this.props.multiple ? [] : _this.props.value || ''
    };
    return _this;
  }

  _createClass(SelectMultipleSimple, [{
    key: "render",
    value: function render() {
      var props = this.props;
      return React__default.createElement("div", {
        className: "SelectMultipleSimple"
      }, React__default.createElement("select", {
        value: this.state.value,
        onChange: this.handleChange,
        disabled: this.props.isDisabled,
        multiple: true
      }, props.options.map(function (option) {
        return React__default.createElement("option", {
          key: option.value.toString(),
          value: option.value,
          disabled: option.isDisabled
        }, React__default.createElement("div", null, option.title || (typeof option.value === 'string' ? option.value : '')));
      })));
    }
  }]);

  return SelectMultipleSimple;
}(React.Component);

_defineProperty(SelectMultipleSimple, "defaultProps", {
  onChange: function onChange() {}
});

SelectMultipleSimple.propTypes = {
  multiple: propTypes.bool,
  onChange: propTypes.func,
  value: propTypes.any,
  isDisabled: propTypes.bool,
  options: propTypes.arrayOf(propTypes.shape({
    name: propTypes.string,
    value: propTypes.any,
    isDisabled: propTypes.bool
  }))
};

var withContextLogic = function withContextLogic(ContextButton) {
  var _class, _temp;

  return _temp = _class =
  /*#__PURE__*/
  function (_Component) {
    _inherits(StandardMenuSimple, _Component);

    function StandardMenuSimple() {
      var _getPrototypeOf2;

      var _this;

      _classCallCheck(this, StandardMenuSimple);

      for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
        args[_key] = arguments[_key];
      }

      _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(StandardMenuSimple)).call.apply(_getPrototypeOf2, [this].concat(args)));

      _defineProperty(_assertThisInitialized(_this), "state", {
        options: _this.props.options,
        isActive: _this.props.isActive,
        isOpen: false
      });

      _defineProperty(_assertThisInitialized(_this), "mouseEnterItem", function (e) {
        if (e.target.value) {
          var newOptions = _this.updateActive(e.target.value.split(','), clone_1(_this.props.options), 0);

          _this.setState({
            options: newOptions
          });
        }
      });

      _defineProperty(_assertThisInitialized(_this), "addBlurListener", function () {
        document.body.addEventListener('click', _this.handleBlur);
        document.body.addEventListener('mousedown', _this.handleBlur);
      });

      _defineProperty(_assertThisInitialized(_this), "removeBlurListener", function () {
        document.body.removeEventListener('click', _this.handleBlur);
        document.body.removeEventListener('mousedown', _this.handleBlur);
      });

      _defineProperty(_assertThisInitialized(_this), "buttonClick", function () {
        if (_this.state.isOpen) {
          _this.removeBlurListener();

          _this.setState({
            isOpen: false,
            options: _this.props.options
          });
        } else {
          _this.addBlurListener();

          _this.setState({
            isOpen: true,
            options: _this.props.options
          });
        }
      });

      _defineProperty(_assertThisInitialized(_this), "handleEvent", function (newState) {
        return function (onEvent) {
          return function (e) {
            if (onEvent) {
              onEvent(e);
            }

            if (newState) {
              _this.setState(newState);
            }
          };
        };
      });

      _defineProperty(_assertThisInitialized(_this), "handleContextMenu", function (e) {
        return _this.handleEvent({
          isOpen: true
        })(_this.props.onContextMenu)(e);
      });

      _defineProperty(_assertThisInitialized(_this), "handleBlur", function (e) {
        if (_this.el && !_this.el.contains(e.target)) {
          _this.handleEvent({
            isOpen: false,
            options: _this.props.options
          })(_this.props.onBlur)(e);
        }
      });

      _defineProperty(_assertThisInitialized(_this), "handleSelectionClose", _this.handleEvent({
        isOpen: false,
        options: _this.props.options
      }));

      return _this;
    }

    _createClass(StandardMenuSimple, [{
      key: "updateActive",
      value: function updateActive(activeFields, newOptions) {
        var _this2 = this;

        var idx = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : 0;

        if (activeFields.length <= idx) {
          return newOptions;
        }

        var changeIdx = newOptions.findIndex(function (option, optIdx) {
          if (Array.isArray(option)) {
            var subIdx = option.findIndex(function (opt) {
              return opt.title === activeFields[idx];
            });

            if (subIdx !== -1) {
              newOptions[optIdx][subIdx].isActive = true;

              if (newOptions[optIdx][subIdx].options) {
                newOptions[optIdx][subIdx].options = _this2.updateActive(activeFields, newOptions[optIdx][subIdx].options, idx + 1);
              }

              return;
            }
          }

          return option.title === activeFields[idx];
        });

        if (changeIdx !== -1) {
          newOptions[changeIdx].isActive = true;
          newOptions[changeIdx].options = this.updateActive(activeFields, newOptions[changeIdx].options, idx + 1);
        }

        return newOptions;
      }
    }, {
      key: "render",
      value: function render() {
        var _this3 = this;

        var renderedMenu = React__default.createElement(StandardMenu, {
          options: this.state.options,
          className: "renderedMenu",
          mouseEnterItem: function mouseEnterItem(e) {
            return _this3.mouseEnterItem(e);
          },
          closeOnClick: this.handleSelectionClose
        });

        if (ContextButton) {
          var _this$props = this.props,
              className = _this$props.className,
              props = _objectWithoutProperties(_this$props, ["className"]);

          return React__default.createElement("div", {
            ref: function ref(el) {
              _this3.el = el;
            },
            className: cx('StandardMenuWrapper', className, {
              active: this.state.isOpen
            })
          }, React__default.createElement(ContextButton, _extends$1({}, props, {
            onClick: this.buttonClick,
            className: this.state.isOpen ? 'active' : '',
            onContextMenu: this.props.onContextMenu && function (e) {
              return _this3.handleContextMenu(e);
            }
          }), props.children), renderedMenu);
        }

        return renderedMenu;
      }
    }], [{
      key: "getDerivedStateFromProps",
      value: function getDerivedStateFromProps(nextProps, prevState) {
        if (nextProps.isActive !== prevState.isActive) {
          return {
            options: nextProps.options,
            isActive: nextProps.isActive
          };
        } else return null;
      }
    }]);

    return StandardMenuSimple;
  }(React.Component), _defineProperty(_class, "defaultProps", {
    value: []
  }), _defineProperty(_class, "propTypes", _objectSpread({}, standardMenuProps$1, {
    onClick: propTypes.func,
    onBlur: propTypes.func,
    onContextMenu: propTypes.func
  })), _temp;
};

var Started = withContextLogic(StartButton);

var StartMenu = function StartMenu(props) {
  var className = props.className,
      otherProps = _objectWithoutProperties(props, ["className"]);

  return React__default.createElement(Started, _extends$1({
    className: cx('StartMenu', className)
  }, otherProps));
};

StartMenu.propTypes = Started.propTypes;

var Notifier = function Notifier(props) {
  return React__default.createElement("button", {
    className: "btn Notifier TaskBar__notifications__notifier",
    title: props.title,
    onClick: props.onClick,
    style: {
      backgroundImage: "url(\"".concat(props.icon, "\")")
    }
  });
};

Notifier.propTypes = {
  icon: propTypes.string,
  onClick: propTypes.func,
  title: propTypes.string
};
Notifier.defaultProps = {
  onClick: function onClick() {}
};

var INTERVALS = 20000;

var formatTime = function formatTime(date) {
  var hour = date.getHours();
  var min = date.getMinutes();

  if (hour < 10) {
    hour = '0' + hour;
  }

  if (min < 10) {
    min = '0' + min;
  }

  return hour + ':' + min;
};

var Time =
/*#__PURE__*/
function (_React$Component) {
  _inherits(Time, _React$Component);

  function Time() {
    var _getPrototypeOf2;

    var _this;

    _classCallCheck(this, Time);

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(Time)).call.apply(_getPrototypeOf2, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this), "state", {
      time: _this.props.time ? new Date(_this.props.time) : new Date()
    });

    return _this;
  }

  _createClass(Time, [{
    key: "componentDidMount",
    value: function componentDidMount() {
      var _this2 = this;

      if (!this.props.fixedTime) {
        this.timerId = setInterval(function () {
          _this2.getDate();
        }, INTERVALS);
      }
    }
  }, {
    key: "componentWillUnmount",
    value: function componentWillUnmount() {
      if (this.timerId) {
        clearInterval(this.timerId);
      }
    }
  }, {
    key: "getDate",
    value: function getDate() {
      this.setState({
        time: new Date(this.state.time.getTime() + INTERVALS)
      });
    }
  }, {
    key: "render",
    value: function render() {
      return React__default.createElement("div", {
        className: "TaskBar__notifications__time"
      }, formatTime(this.state.time));
    }
  }]);

  return Time;
}(React__default.Component);

var Notifications = function Notifications(props) {
  return React__default.createElement("div", {
    className: "TaskBar__notifications"
  }, props.notifiers.map(function (notifier) {
    return React__default.createElement(Notifier, {
      key: notifier.alt,
      icon: notifier.icon,
      onClick: notifier.onClick,
      title: notifier.alt
    });
  }), React__default.createElement(Time, null));
};

Notifications.propsTypes = {
  notifiers: propTypes.arrayOf(propTypes.shape(Notifier.propTypes))
};
Notifications.defaultProps = {
  notifiers: []
};

var css$k = ".TaskBar {\n  position: fixed;\n  background-color: #bbc3c4;\n  bottom: 0px;\n  left: 0px;\n  width: 100%;\n  max-width: 100%;\n  z-index: 10;\n  box-shadow: 0px -1px 0px #ffffff;\n  padding: 2px 0px;\n  display: flex; }\n  .TaskBar > div,\n  .TaskBar > button {\n    position: relative;\n    height: 22px;\n    margin: 0px 2px; }\n  .TaskBar > div:not(:last-child) {\n    padding: 0px 6px; }\n    .TaskBar > div:not(:last-child):first-child {\n      padding: 0px 3px 0px 0px; }\n    .TaskBar > div:not(:last-child):after {\n      position: absolute;\n      top: 1px;\n      right: 0px;\n      height: calc(100% - 2px);\n      width: 1px;\n      background-color: #808088;\n      content: \"\";\n      box-shadow: 1px 0px 0px #ffffff; }\n    .TaskBar > div:not(:last-child):before {\n      position: absolute;\n      top: 3px;\n      right: -6px;\n      height: calc(100% - 6px);\n      width: 3px;\n      background-color: #bbc3c4;\n      content: \"\";\n      box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px #ffffff; }\n  .TaskBar__programs {\n    display: flex;\n    flex-grow: 1;\n    flex-shrink: 1;\n    flex-wrap: nowrap;\n    margin-right: 4px;\n    min-width: 42px; }\n    .TaskBar__programs:before {\n      display: none; }\n  .TaskBar__start {\n    position: relative; }\n    .TaskBar__start > button + div {\n      position: fixed;\n      bottom: 25px;\n      left: 2px;\n      visibility: hidden;\n      max-height: 0px;\n      padding-left: 22px; }\n      @media (min-height: 720px) and (min-width: 960px) {\n        .TaskBar__start > button + div {\n          transition: max-height linear 200ms; } }\n      .TaskBar__start > button + div > .divider:empty,\n      .TaskBar__start > button + div > div:empty {\n        margin-left: 24px;\n        width: calc(100% - 26px); }\n      .TaskBar__start > button + div:after {\n        content: \"\";\n        display: block;\n        position: absolute;\n        left: 3px;\n        top: 3px;\n        height: calc(100% - 6px);\n        width: 20px;\n        background: #0000a2;\n        background: linear-gradient(#0000a2, #126fc2);\n        background: url(\"data:image/gif;base64,R0lGODlhDgBkALMAAAAAAP///wIAsZKSmZKTmpGSmZKTmcjOz8fNzsfOz8fOzv///wAAAAAAAAAAAAAAACH5BAEAAAsALAAAAAAOAGQAAAT/cMk5SUo06CO179wSGEowgEOQBcRUEuqkUaIRd/cCwyvFzyJNS3JQ2Tyt0QLBklgwEqZGQasShr4DQhuilDxgRCWAINgIAkIxFoB2DDJWbmGb2Oq0nJx2dqoCXUEuKl8GMCZRSjpgWAdYEydVkhMJQlVkQR8UTFRgQDhiHkc9QRyfRwRSV5+ZH1KbnodzjEGPCAYFcBIJj5mOk61IkgZSnpKVxpSeYCuegTjCw8Uev1bLPkfXccuY29SSGgmRky2p4b2Jnm5+3LrQ3CsY5Wuk9ZlwcJrv2uzLvWthJgH0cWVAKkMGBjhKws1YQ4cPP1wxUETclUPuBOXRY4mOvmDJafaFFMmKwoEDCspIgnGSC0pYDZvB88YvE7Bd3YABrBlRJs+HN73MiPgq4heQYJAhlYiOhqyUwLhVo7TTWcYlyEZOmAbEYM+I4hape4b0Cg0tDXlVyapVR9UY5h7KaogAg9R1c82ubEohAgA7\") no-repeat bottom 3px center, linear-gradient(#0000a2, #126fc2); }\n      .TaskBar__start > button + div > div {\n        display: flex;\n        align-items: center;\n        margin-left: 20px; }\n        .TaskBar__start > button + div > div > button {\n          height: 32px;\n          padding-left: 32px;\n          background-size: 22px;\n          background-position: 4px center; }\n    .TaskBar__start > button.active, .TaskBar__start > button.clicked {\n      background-position: 3px 2px;\n      outline: 1px dotted #0c0c0c;\n      outline-offset: -4px; }\n      .TaskBar__start > button.active > div, .TaskBar__start > button.clicked > div {\n        visibility: visible;\n        max-height: 100vh;\n        padding: 3px; }\n        .TaskBar__start > button.active > div div, .TaskBar__start > button.clicked > div div {\n          display: flex; }\n    .TaskBar__start.active > div {\n      visibility: visible;\n      max-height: 100vh;\n      padding: 3px; }\n      .TaskBar__start.active > div div {\n        display: flex; }\n  .TaskBar__notifications {\n    background-color: #bbc3c4;\n    display: flex;\n    flex: none;\n    margin-left: auto;\n    align-items: center;\n    height: 22px;\n    padding: 0px 8px 0px 4px;\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #808088; }\n    .TaskBar__notifications__time {\n      margin-left: 4px; }\n    .TaskBar__notifications__notifier {\n      height: 16px;\n      width: 16px;\n      background-color: #bbc3c4;\n      background-size: contain;\n      background-position: center;\n      background-repeat: no-repeat;\n      border: none; }\n      .TaskBar__notifications__notifier:active, .TaskBar__notifications__notifier:focus, .TaskBar__notifications__notifier:active:focus, .TaskBar__notifications__notifier.active, .TaskBar__notifications__notifier.clicked {\n        outline: none;\n        border: none; }\n";
styleInject(css$k);

var TaskBar = function TaskBar(props) {
  return React__default.createElement("div", {
    className: "TaskBar"
  }, React__default.createElement(StartMenu, {
    className: "TaskBar__start",
    options: props.options
  }), props.quickLaunch && React__default.createElement("div", {
    className: "TaskBar__quick-launch"
  }, props.quickLaunch.map(function (qlEntry) {
    return React__default.createElement(ButtonIconSmall, {
      key: "".concat(qlEntry.icon, "-QuickLaunch"),
      title: qlEntry.title,
      onClick: qlEntry.onClick,
      icon: qlEntry.icon
    });
  })), React__default.createElement("div", {
    className: "TaskBar__programs"
  }, props.openWindows && props.openWindows.map(function (openWindow) {
    return React__default.createElement(ButtonProgram, {
      isActive: openWindow.isActive,
      onClick: openWindow.onClick,
      icon: openWindow.icon,
      key: "".concat(openWindow.icon, "-ButtonProgram-").concat(openWindow.title)
    }, openWindow.title);
  })), React__default.createElement(Notifications, {
    notifiers: props.notifiers
  }));
};

TaskBar.propTypes = {
  options: propTypes.array,
  quickLaunch: propTypes.arrayOf(propTypes.shape(ButtonIconSmall.propTypes)),
  openWindows: propTypes.arrayOf(propTypes.shape(ButtonProgram.propTypes)),
  notifiers: propTypes.arrayOf(propTypes.shape(Notifications.propsTypes))
};

var css$l = ".w98 .Window__heading {\n  display: flex;\n  background: linear-gradient(to right, #0000a2, #126fc2);\n  font-weight: bold;\n  color: #ffffff;\n  margin-bottom: 1px;\n  padding: 0px 1px 0px 3px;\n  align-items: center;\n  letter-spacing: 1px; }\n  .w98 .Window__heading button {\n    padding: 0px;\n    min-width: initial;\n    width: 16px;\n    height: 14px;\n    margin-left: 1px;\n    image-rendering: pixelated;\n    display: flex;\n    align-items: center;\n    flex-shrink: 0;\n    background-repeat: no-repeat;\n    background-position: 1px 1px; }\n    .w98 .Window__heading button:focus, .w98 .Window__heading button.clicked {\n      outline: none;\n      border: none; }\n    .w98 .Window__heading button:active:focus, .w98 .Window__heading button.clicked {\n      padding: 2px 8px 1px 4px;\n      background-position: 2px 2px; }\n\n.w98 .Window__icon {\n  padding: 8px;\n  display: flex;\n  background-size: 14px;\n  background-repeat: no-repeat;\n  background-position: center;\n  margin-right: 4px; }\n\n.w98 .Window__title {\n  white-space: nowrap;\n  overflow: hidden;\n  text-overflow: ellipsis;\n  flex-grow: 1;\n  min-width: 0px;\n  user-select: none; }\n\n.w98 .Window__close {\n  margin-left: 2px;\n  background-image: url(\"data:image/gif;base64,R0lGODlhDQALAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAANAAsAAAIUlI+pKwDoVGxvucmwvblqo33MqBQAOw==\"); }\n\n.w98 .Window__restore {\n  background-image: url(\"data:image/gif;base64,R0lGODlhDQALAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAANAAsAAAIZlI9pwK3SnAKI1kjtwTlpyHjV830b9qRHAQA7\"); }\n\n.w98 .Window__minimize {\n  background-image: url(\"data:image/gif;base64,R0lGODlhDQALAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAANAAsAAAIOlI+py+0PozSg2mXvFAUAOw==\"); }\n\n.w98 .Window__maximize {\n  background-image: url(\"data:image/gif;base64,R0lGODlhDQALAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAANAAsAAAIXlI8Jy4wNXzJAznqwsjtPoYFfCDXfWQAAOw==\"); }\n\n.w98 .Window--resizable:after {\n  position: absolute;\n  bottom: 4px;\n  right: 4px;\n  height: 12px;\n  width: 12px;\n  content: \"\";\n  background-image: url(\"data:image/gif;base64,R0lGODlhDAAMAJEAAAAAAP///5mZmf///yH5BAEAAAMALAAAAAAMAAwAAAIbnI8TmSF83IMSKvFWw3dnHnFV+GVGhZZXmaoFADs=\"); }\n\n.w98 .Window--maximized {\n  width: 100%;\n  height: 100%; }\n\n.w98 .Window--drag {\n  background-color: rgba(0, 0, 0, 0);\n  box-shadow: inset -3px -3px 0px #808088, inset 3px 3px 0px #808088; }\n  .w98 .Window--drag > *, .w98 .Window--drag:after {\n    filter: opacity(0.1%); }\n";
styleInject(css$l);

var WindowAbstract =
/*#__PURE__*/
function (_Component) {
  _inherits(WindowAbstract, _Component);

  function WindowAbstract() {
    var _getPrototypeOf2;

    var _this;

    _classCallCheck(this, WindowAbstract);

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(WindowAbstract)).call.apply(_getPrototypeOf2, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this), "state", {
      maximized: _this.props.maximizeOnOpen
    });

    _defineProperty(_assertThisInitialized(_this), "handleMaximize", function (e) {
      _this.setState({
        maximized: true
      });

      if (_this.props.onMaximize) {
        _this.props.onMaximize(e);
      }
    });

    _defineProperty(_assertThisInitialized(_this), "handleRestore", function (e) {
      _this.setState({
        maximized: false
      });

      if (_this.props.onRestore) {
        _this.props.onRestore(e);
      }
    });

    return _this;
  }

  _createClass(WindowAbstract, [{
    key: "render",
    value: function render() {
      var props = this.props;
      return React__default.createElement(WindowFrame, {
        className: cx('Window', props.className, {
          'Window--maximized': this.state.maximized,
          'Window--resizable': props.resizable,
          'Window--drag': props.changingState
        }),
        ref: props.innerRef
      }, React__default.createElement("div", {
        className: "Window__heading"
      }, props.icon && React__default.createElement("div", {
        className: "Window__icon",
        style: {
          backgroundImage: "url('".concat(props.icon, "')")
        }
      }), React__default.createElement("div", {
        className: "Window__title"
      }, props.title), props.onHelp && React__default.createElement(ButtonNav, {
        className: "Window__help",
        onClick: props.onHelp
      }), props.onMinimize && React__default.createElement(ButtonNav, {
        className: "Window__minimize",
        onClick: props.onMinimize
      }), this.state.maximized && this.props.resizable && React__default.createElement(ButtonNav, {
        className: "Window__restore",
        onClick: this.handleRestore
      }), !this.state.maximized && this.props.resizable && React__default.createElement(ButtonNav, {
        className: "Window__maximize",
        onClick: this.handleMaximize
      }), (props.onClose || props.onMaximize || props.onRestore || props.onMinimize || props.onHelp) && React__default.createElement(ButtonNav, {
        className: "Window__close",
        onClick: props.onClose,
        isDisabled: !props.onClose
      })), props.children);
    }
  }]);

  return WindowAbstract;
}(React.Component);

_defineProperty(WindowAbstract, "defaultProps", {
  title: '...',
  resizable: true
});

var windowProps = {
  children: propTypes.node,
  title: propTypes.string,
  className: propTypes.string,
  isActive: propTypes.bool,
  icon: propTypes.string,
  onClose: propTypes.func,
  onMinimize: propTypes.func,
  onMaximize: propTypes.func,
  onRestore: propTypes.func,
  maximizeOnOpen: propTypes.bool,
  changingState: propTypes.bool
};
WindowAbstract.propTypes = windowProps;

var css$m = ".WindowAlert {\n  display: inline-flex;\n  flex-direction: column;\n  max-width: 250px; }\n  .WindowAlert__message {\n    display: flex;\n    align-items: center;\n    user-select: none;\n    min-height: 28px;\n    padding: 10px 2px 6px; }\n    .WindowAlert__message.has-icon {\n      background-size: 28px 28px;\n      background-repeat: no-repeat;\n      background-position: 6px 6px;\n      padding: 6px 4px 8px 40px; }\n  .WindowAlert__actions {\n    width: 100%;\n    display: flex;\n    justify-content: center; }\n    .WindowAlert__actions .btn {\n      margin: 0px 4px 8px; }\n";
styleInject(css$m);

var WindowAlert = function WindowAlert(props) {
  return React__default.createElement(WindowAbstract, {
    className: cx('WindowAlert', props.className),
    onClose: props.onClose,
    onHelp: props.onHelp,
    title: props.title || 'Error',
    resizable: false
  }, React__default.createElement("div", {
    className: cx('WindowAlert__message', {
      'has-icon': props.icon
    }),
    style: props.icon && {
      backgroundImage: "url(".concat(props.icon, ")")
    }
  }, props.children), React__default.createElement("div", {
    className: "WindowAlert__actions"
  }, props.onOK && React__default.createElement(ButtonForm, {
    className: "WindowAlert__ok",
    onClick: props.onOK
  }, "OK"), props.onCancel && React__default.createElement(ButtonForm, {
    className: "WindowAlert__cancel",
    onClick: props.onCancel
  }, "Cancel")));
};

WindowAlert.propTypes = _objectSpread({}, WindowAbstract.propTypes, {
  onOK: propTypes.func,
  onCancel: propTypes.func,
  children: propTypes.node,
  icon: propTypes.string
});

var css$n = ".MenuBar {\n  display: flex;\n  padding: 0px;\n  font-size: 1rem;\n  position: relative;\n  overflow-y: visible;\n  z-index: 20; }\n  .MenuBar > div {\n    position: relative; }\n    .MenuBar > div > button {\n      padding: 0px 4px;\n      outline: none;\n      border: none;\n      user-select: none;\n      color: #0c0c0c;\n      display: inline-block;\n      background-color: rgba(0, 0, 0, 0);\n      width: 100%;\n      overflow: hidden;\n      white-space: nowrap;\n      text-overflow: ellipsis;\n      text-align: left;\n      padding: 3px 6px; }\n      .MenuBar > div > button + div,\n      .MenuBar > div > button + div {\n        z-index: 20;\n        visibility: hidden;\n        position: absolute;\n        max-height: 0px;\n        top: 100%;\n        left: 0px; }\n        @media (min-height: 720px) and (min-width: 960px) {\n          .MenuBar > div > button + div,\n          .MenuBar > div > button + div {\n            transition: max-height linear 750ms; } }\n      .MenuBar > div > button:hover {\n        box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px #ffffff; }\n      .MenuBar > div > button:active, .MenuBar > div > button:focus, .MenuBar > div > button:active:focus, .MenuBar > div > button.active, .MenuBar > div > button.clicked {\n        box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #808088;\n        padding: 4px 5px 2px 7px; }\n        .MenuBar > div > button:active + div,\n        .MenuBar > div > button:active + div, .MenuBar > div > button:focus + div,\n        .MenuBar > div > button:focus + div, .MenuBar > div > button:active:focus + div,\n        .MenuBar > div > button:active:focus + div, .MenuBar > div > button.active + div,\n        .MenuBar > div > button.active + div, .MenuBar > div > button.clicked + div,\n        .MenuBar > div > button.clicked + div {\n          visibility: visible;\n          max-height: 480px; }\n";
styleInject(css$n);

var MenuEntry = withContextLogic(AbstractButton);

var MenuBar = function MenuBar(props) {
  return React__default.createElement("menu", {
    className: "window__menu MenuBar"
  }, props.options && props.options.map(function (section) {
    return React__default.createElement(MenuEntry, {
      className: cx('MenuBar__section', props.className),
      key: "menu-bar-section-".concat(section.title),
      options: section.options
    }, section.title);
  }));
};

MenuBar.propTypes = {
  options: propTypes.arrayOf(propTypes.shape()),
  className: propTypes.string
};

var css$o = ".w98 .WindowProgram {\n  display: inline-flex;\n  flex-direction: column; }\n  .w98 .WindowProgram > footer {\n    display: flex; }\n    .w98 .WindowProgram > footer > div {\n      white-space: nowrap;\n      text-overflow: ellipsis;\n      overflow: hidden;\n      min-width: 0px;\n      flex-grow: 1;\n      padding: 2px;\n      height: 12px;\n      box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #0c0c0c; }\n      .w98 .WindowProgram > footer > div:not(:last-child) {\n        margin-right: 2px; }\n      .w98 .WindowProgram > footer > div:last-child {\n        padding-right: 12px; }\n  .w98 .WindowProgram > div:last-child {\n    margin-top: 2px; }\n";
styleInject(css$o);

var insertDefaultFooter = function insertDefaultFooter(customFooterElements) {
  var minimum = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 2;
  var footer = Array.isArray(customFooterElements) ? _toConsumableArray(customFooterElements) : [];

  for (var i = 0; i < minimum; i++) {
    footer[i] = footer && footer.text ? footer[i] : {
      text: ''
    };
  }

  return footer;
};

var Footer = function Footer() {
  var props = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : [];
  return React__default.createElement("footer", null, props.entries.map(function (entry, idx) {
    return React__default.createElement("div", {
      key: "".concat(entry, "-").concat(idx),
      style: entry.icon && {
        backgroundImage: "url(".concat(entry.icon, ")")
      }
    }, entry.text || '');
  }));
};

var footerType = {
  text: propTypes.string,
  icon: propTypes.string
};
Footer.propTypes = {
  entries: propTypes.arrayOf(propTypes.shape(footerType))
};

var WindowProgram =
/*#__PURE__*/
function (_React$Component) {
  _inherits(WindowProgram, _React$Component);

  function WindowProgram() {
    _classCallCheck(this, WindowProgram);

    return _possibleConstructorReturn(this, _getPrototypeOf(WindowProgram).apply(this, arguments));
  }

  _createClass(WindowProgram, [{
    key: "render",
    value: function render() {
      var props = this.props;
      var footer = insertDefaultFooter(props.footer);
      return React__default.createElement(WindowAbstract, {
        className: cx('WindowProgram', props.className),
        icon: props.icon,
        onClose: props.onClose,
        onMinimize: props.onMinimize,
        onMaximize: props.onMaximize,
        onRestore: props.onRestore,
        title: props.title,
        resizable: props.resizable,
        changingState: props.changingState,
        maximizeOnOpen: props.maximizeOnOpen
      }, Array.isArray(props.menuOptions) && React__default.createElement(MenuBar, {
        className: "WindowProgram__menu",
        options: props.menuOptions
      }), props.children, props.footer && React__default.createElement(Footer, {
        entries: footer
      }));
    }
  }]);

  return WindowProgram;
}(React__default.Component);

_defineProperty(WindowProgram, "defaultProps", {
  onMaximize: function onMaximize() {}
});

WindowProgram.propTypes = _objectSpread({}, WindowAbstract.propTypes, {
  menuOptions: propTypes.arrayOf(propTypes.any),
  footer: propTypes.arrayOf(propTypes.shape(footerType))
});

var css$p = ".OptionsList {\n  max-height: 40px;\n  z-index: 10; }\n  .OptionsList__large-icons {\n    display: flex;\n    overflow: hidden; }\n  .OptionsList__dropdown {\n    position: absolute;\n    right: 2px;\n    top: 2px;\n    height: calc(100% - 4px); }\n    .OptionsList__dropdown--empty {\n      display: none; }\n    .OptionsList__dropdown__button {\n      height: 100%;\n      border: none;\n      background-color: #bbc3c4;\n      background-image: url(\"data:image/gif;base64,R0lGODlhCAAFAJEAAAAAAP///////wAAACH5BAEAAAIALAAAAAAIAAUAAAIKBCSGebzqoJKtAAA7\");\n      background-repeat: no-repeat;\n      background-position: 2px 3px;\n      padding: 0px 6px;\n      font-size: 0.7rem;\n      user-select: none;\n      letter-spacing: -2px;\n      display: flex;\n      flex-direction: column; }\n      .OptionsList__dropdown__button:hover {\n        box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px #ffffff; }\n      .OptionsList__dropdown__button:active, .OptionsList__dropdown__button:focus, .OptionsList__dropdown__button:active:focus {\n        outline: none;\n        background-position: 3px 4px;\n        box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #808088; }\n        .OptionsList__dropdown__button:active + .OptionsList__dropdown__list, .OptionsList__dropdown__button:focus + .OptionsList__dropdown__list, .OptionsList__dropdown__button:active:focus + .OptionsList__dropdown__list {\n          position: absolute;\n          top: 100%;\n          right: 0px;\n          display: block;\n          z-index: 10; }\n  .OptionsList .OptionsList__dropdown__list {\n    display: none; }\n  .OptionsList .OptionsList__dropdown__button {\n    margin-left: auto; }\n  .OptionsList .StandardMenuItem__button:hover {\n    background-color: #0000a2;\n    color: #ffffff; }\n  .OptionsList .divider {\n    border-left: 1px solid #808088;\n    border-right: 1px solid #ffffff;\n    width: 1px;\n    margin: 2px 3px; }\n    .OptionsList .divider + .divider {\n      display: none; }\n";
styleInject(css$p);

var OptionsListDropdown =
/*#__PURE__*/
function (_Component) {
  _inherits(OptionsListDropdown, _Component);

  function OptionsListDropdown() {
    var _getPrototypeOf2;

    var _this;

    _classCallCheck(this, OptionsListDropdown);

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _possibleConstructorReturn(this, (_getPrototypeOf2 = _getPrototypeOf(OptionsListDropdown)).call.apply(_getPrototypeOf2, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this), "openList", function () {
      _this.dropdownButton.focus();
    });

    return _this;
  }

  _createClass(OptionsListDropdown, [{
    key: "render",
    value: function render() {
      var _this2 = this;

      return React__default.createElement("div", {
        className: "OptionsList__dropdown"
      }, React__default.createElement("button", {
        ref: function ref(btn) {
          _this2.dropdownButton = btn;
        },
        onClick: this.openList,
        className: "OptionsList__dropdown__button"
      }), React__default.createElement(StandardMenu, {
        className: "OptionsList__dropdown__list",
        options: this.props.options
      }));
    }
  }]);

  return OptionsListDropdown;
}(React.Component);

var OptionsList =
/*#__PURE__*/
function (_Component2) {
  _inherits(OptionsList, _Component2);

  function OptionsList() {
    var _getPrototypeOf3;

    var _this3;

    _classCallCheck(this, OptionsList);

    for (var _len2 = arguments.length, args = new Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
      args[_key2] = arguments[_key2];
    }

    _this3 = _possibleConstructorReturn(this, (_getPrototypeOf3 = _getPrototypeOf(OptionsList)).call.apply(_getPrototypeOf3, [this].concat(args)));

    _defineProperty(_assertThisInitialized(_this3), "state", {
      entriesInView: 8
    });

    _defineProperty(_assertThisInitialized(_this3), "ref", React__default.createRef());

    _defineProperty(_assertThisInitialized(_this3), "checkWidth", function () {
      if (!_this3.ref.current) {
        return;
      }

      var width = _this3.ref.current.offsetWidth || 200;
      var entriesInView = (width - 20) / 50;

      if (_this3.state.entriesInView !== entriesInView) {
        _this3.setState({
          entriesInView: entriesInView
        });
      }
    });

    return _this3;
  }

  _createClass(OptionsList, [{
    key: "render",
    value: function render() {
      var _this4 = this;

      var props = this.props,
          state = this.state;
      var options = flattenWithDividers(props.options);
      return React__default.createElement("menu", {
        ref: this.ref,
        onMouseEnter: function onMouseEnter() {
          return _this4.checkWidth();
        },
        className: cx(props.className, 'OptionsList')
      }, React__default.createElement("div", {
        className: "OptionsList__large-icons"
      }, options.slice(0, state.entriesInView).map(function (option) {
        if (option.includes && option.includes('divider')) {
          return React__default.createElement("div", {
            className: "divider ".concat(option)
          });
        }

        return React__default.createElement(ButtonIconLarge, {
          key: "large-button-".concat(option.title),
          icon: option.icon,
          title: option.title,
          onClick: function onClick() {
            return _this4.setState({
              rand: Math.random()
            });
          },
          isDisabled: !option.onClick
        });
      })), props.options.slice(state.entriesInView).length > 0 && React__default.createElement(OptionsListDropdown, {
        options: props.options.slice(state.entriesInView)
      }));
    }
  }]);

  return OptionsList;
}(React.Component);

_defineProperty(OptionsList, "propTypes", {
  options: propTypes.arrayOf(propTypes.shape(ButtonIconLarge.propTypes)),
  className: propTypes.string
});

var css$q = ".w98 .WindowExplorer {\n  display: inline-flex;\n  flex-direction: column; }\n  .w98 .WindowExplorer__view {\n    min-height: 20px;\n    margin: 2px 0px;\n    flex-grow: 1;\n    background-color: #ffffff;\n    box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c; }\n  .w98 .WindowExplorer__details {\n    display: flex; }\n    .w98 .WindowExplorer__details__section {\n      box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #808088;\n      flex-grow: 1;\n      margin-top: 2px;\n      height: 16px; }\n      .w98 .WindowExplorer__details__section:not(:last-child) {\n        margin: 2px; }\n  .w98 .WindowExplorer .window__menu {\n    padding: 2px 2px 2px 12px; }\n  .w98 .WindowExplorer > div + menu {\n    margin-top: 2px;\n    box-shadow: 0px 2px 0px -1px #ffffff, -1px 2px 0px -1px #ffffff, -1px 1px 0px #808088, 0px 1px 0px #808088, inset 0px -1px 0px #808088, inset -1px 0px 0px #808088, inset 0px 0px 0px 1px #ffffff, -1px 0px 0px #808088, 1px 0px 0px #ffffff, -1px 1px 0px 0px #ffffff, 1px 1px 0px 0px #ffffff, -1px -1px 0px #808088, 0px -1px 0px #808088, inset 0px 1px 0px #ffffff, 1px -1px 0px #ffffff; }\n  .w98 .WindowExplorer > menu {\n    position: relative;\n    padding-left: 12px;\n    margin: 0px 1px;\n    display: flex;\n    box-shadow: inset 0px -1px 0px #808088, inset -1px 0px 0px #808088, inset 0px 0px 0px 1px #ffffff, -1px 0px 0px #808088, 1px 0px 0px #ffffff, -1px 1px 0px 0px #ffffff, 1px 1px 0px 0px #ffffff; }\n    .w98 .WindowExplorer > menu:before {\n      position: absolute;\n      top: 3px;\n      left: 5px;\n      height: calc(100% - 6px);\n      width: 3px;\n      background-color: #bbc3c4;\n      content: \"\";\n      box-shadow: inset -1px -1px 0px #808088, inset 1px 1px 0px #ffffff; }\n  .w98 .WindowExplorer > footer {\n    display: flex; }\n    .w98 .WindowExplorer > footer > div {\n      white-space: nowrap;\n      text-overflow: ellipsis;\n      overflow: hidden;\n      min-width: 0px;\n      flex-grow: 1;\n      padding: 2px;\n      height: 12px;\n      box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px #0c0c0c; }\n      .w98 .WindowExplorer > footer > div:not(:last-child) {\n        margin-right: 2px; }\n      .w98 .WindowExplorer > footer > div:last-child {\n        padding-right: 12px; }\n  .w98 .WindowExplorer__address {\n    display: flex;\n    height: 26px;\n    overflow-y: visible;\n    user-select: none; }\n    .w98 .WindowExplorer__address__title {\n      align-self: center;\n      margin-right: 4px; }\n    .w98 .WindowExplorer__address .FakeSelect {\n      flex-grow: 1;\n      z-index: 5;\n      margin-right: 4px; }\n  .w98 .WindowExplorer__options {\n    display: flex;\n    padding: 2px 8px 2px 12px; }\n  .w98 .WindowExplorer > div:last-child {\n    margin-top: 2px; }\n";
styleInject(css$q);

var WindowExplorer =
/*#__PURE__*/
function (_React$Component) {
  _inherits(WindowExplorer, _React$Component);

  function WindowExplorer() {
    _classCallCheck(this, WindowExplorer);

    return _possibleConstructorReturn(this, _getPrototypeOf(WindowExplorer).apply(this, arguments));
  }

  _createClass(WindowExplorer, [{
    key: "render",
    value: function render() {
      var props = this.props;
      return React__default.createElement(WindowProgram, {
        className: cx('WindowExplorer', props.className),
        icon: props.icon,
        onClose: props.onClose,
        onMinimize: props.onMinimize,
        onMaximize: props.onMaximize,
        onRestore: props.onRestore,
        title: props.title,
        resizable: props.resizable,
        footer: props.footer,
        menuOptions: props.menuOptions,
        maximizeOnOpen: props.maximizeOnOpen,
        changingState: props.changingState
      }, props.explorerOptions && React__default.createElement(OptionsList, {
        className: "WindowExplorer__options",
        options: props.explorerOptions
      }), React__default.createElement("menu", {
        className: "WindowExplorer__address"
      }, React__default.createElement("div", {
        className: "WindowExplorer__address__title"
      }, "Address"), props.customSelect ? props.customSelect() : React__default.createElement(FakeSelect, {
        title: props.title,
        icon: props.icon,
        isDisabled: true
      })), React__default.createElement("div", {
        className: "WindowExplorer__view"
      }, props.children));
    }
  }]);

  return WindowExplorer;
}(React__default.Component);

_defineProperty(WindowExplorer, "defaultProps", {
  footer: [],
  menuOptions: []
});

WindowExplorer.propTypes = _objectSpread({}, WindowProgram.propTypes, {
  explorerOptions: propTypes.shape(OptionsList.propTypes.options)
});

var css$r = ".DetailsSection,\n.window__section {\n  position: relative;\n  border: 1px solid #ffffff;\n  outline: 1px solid #808088;\n  padding: 5px;\n  margin: 16px 8px 8px; }\n  .DetailsSection__title,\n  .window__section__title {\n    position: absolute;\n    top: -10px;\n    padding: 2px 4px;\n    background-color: #bbc3c4; }\n";
styleInject(css$r);

var DetailsSection = function DetailsSection(props) {
  return props.children ? React__default.createElement("section", {
    className: "DetailsSection window__section"
  }, React__default.createElement("div", {
    className: "DetailsSection__title"
  }, props.title), props.children) : null;
};

DetailsSection.propTypes = {
  title: propTypes.node,
  children: propTypes.node
};

var activeDesktop16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAnUExURUdwTFOoqf///wAAAMDHyIeIjxEA/6ipUf7/AKoAVwcAqwD///8AAC/f764AAAABdFJOUwBA5thmAAAAZUlEQVQY012O0RKAIAgEQQ4s6/+/N06trH3bnZsBkYV9lw/1ZFDipG7V3EQPDZSEHpGhO7o3MHQfezSGxYFm4vRSh8MZ0osV2BOMR7AuskxnUNrt8yxeV34auIm+yFd9EMrX7ccF27wDshZIPIoAAAAASUVORK5CYII=";

var calculator16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAMCAMAAABcOc2zAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAVUExURUdwTAcAq1Ooqf///wAAAAD//8DHyDK30YoAAAABdFJOUwBA5thmAAAAP0lEQVQI14XMWwoAIQxD0Zik3f+Sh/FFBcGTv3IpwANARRkNhqc/aAZldbkO4Rx2UX/2gtbeo1DeC7bKgA/4AN3sAhuaJA20AAAAAElFTkSuQmCC";

var computer32Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAB8AAAAgCAMAAADdXFNzAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAhUExURUdwTP///wAAAMDHyIeIj1OoqREA/wD/AACpUwD//wcAq/C1J6kAAAABdFJOUwBA5thmAAAAnUlEQVQoz42SCQ7EIAhFZZnpcv8Dl47Fon7aeTEx8UVAsBRHJ0pEZYCUo6YRjV5pvC6j73PT5DmC/CcA/Vbv5v73iNzb6f41OPceAfuz7id/nj97fwHwb/0bxiN/zOf+AgowLR6CAaavFIrxEua/4z/IvUCQD9E7vyzV3+X1fl27yGl8mN92mhe361CbbVrBemlO660kxV2jUU6o+gBEWAjauUre2gAAAABJRU5ErkJggg==";

var controlPanel16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAANCAMAAABBwMRzAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAbUExURUdwTP///wAAAMDHyP7/AIeIj6oAV/8AABEA/6YT1MsAAAABdFJOUwBA5thmAAAAUElEQVQI11WOwREAIQgDMSFq/xUfCufo8goLA2amhR1Ej9Ibo1FjahdC5PQuwXemYhgMyfQSW1uhPLYBnGd/wkdn+WhMcPTL/zeQ3x5ghocP4sMCX1pY6W4AAAAASUVORK5CYII=";

var folder16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAANCAMAAABBwMRzAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAASUExURUdwTP///wAAAMDHyP7/AIeIj/DYpwIAAAABdFJOUwBA5thmAAAAM0lEQVQI17WKwREAIAjDarH7r2zxOJUBDK+UAFCCg2b41NVDZRoPor2CHaVfjR//BgE2FuJjAlfcks8tAAAAAElFTkSuQmCC";

var folderFavorites24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAUCAMAAACgaw2xAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAYUExURUdwTMDHyP7/AIeIjwAAABEA/////6ipUSZt3z0AAAABdFJOUwBA5thmAAAAYElEQVQY042QUQ6AMAhDC6x6/xu7qRmTgFn5Wl8KAwCwVwgylaes8AMxWWRLVzsytQG8ldfZOkh8vcF8MU10l86WhFDpmc8MkskMDpuTbSREqxnlr8o9/jYPt0rVAVoqXAKxBIZ6OS1eAAAAAElFTkSuQmCC";

var folderOpen24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAWCAMAAADto6y6AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAYUExURUdwTP///wAAAMDHyP7/AIeIj6ipUREA/6MGgeEAAAABdFJOUwBA5thmAAAAc0lEQVQoz3XRWRKAMAgDULbU+99YgboVGsefvJHilOgTUB+o9D1zEXiYi3jn77EIWC37EAAPPH2I2bjh7VOGxMH6zyUOscwvcomD2vJI7oa1N2xF8m/qLEACrJ4S63azJtRZsvlCE7pZE5pZCaNk3oqUEJ1TjwT19CEMmgAAAABJRU5ErkJggg==";

var folderOptions16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAMAAAAMCGV4AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAeUExURUdwTP///wAAAMDHyP7/AIeIjwD//xEA/6ipUQcAq/jryeYAAAABdFJOUwBA5thmAAAAXElEQVQI11WMWxLAIAgDeRil979wE6sdXT+YTUAzg7AftOTDrQzWGtwTCA6CoCe8e2AuyaU9Z/C5tEcdfbKv3TdIUbV6DV6PUaufPz+dgXyjgG6xURB2wOByrtoLU90C2k4z3ToAAAAASUVORK5CYII=";

var folderProgram16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAkUExURUdwTP///wAAAMDHyIeIj/7/AAcAq6oAVwCpUxEA/wD///8AAHXN57cAAAABdFJOUwBA5thmAAAAW0lEQVQY012OWw7AIAgE2QWrtve/b8F3O3wYJpOIiFggG9PkY7/dzQwNB8YQSdd04e+GrTBdcBTXYBZf4cX6RkcBpAzULgLkJ6PcNYSQ9MIDlNLE59opzjsCHrx+sALRFlml9wAAAABJRU5ErkJggg==";

var folderProgram24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAMAAADXqc3KAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAtUExURUdwTP///wAAAMDHyIeIj/7/AAcAq6ipUREA/wCpU6oAV/8AAKlUqgD//wD/AH8xaYIAAAABdFJOUwBA5thmAAAAjUlEQVQoz42Q0RKEIAgABfTSsvv/zw2QtLC7aZ3pgZ1VM4QQjeCIkBrOROrcywge7DvRfS1ows1TF/+KOIGtuFzNQCvocwIoi3rRBSqjeNpKC/eTo3gSVmwrQNZpUbEILLbEYs+iShER5BIsVi0yp+WbVbS3B+J5pVolKFcxHX4Kfh8YnzfFLzE/iYIzBz/HBg1nyTBoAAAAAElFTkSuQmCC";

var help24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAMAAADXqc3KAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAYUExURUdwTAAAAKlUqoeIj8DHyP////7/AKipURimofcAAAABdFJOUwBA5thmAAAAhklEQVQoz23SQRKAIAhAUQCV+984BAU1XDX/GTaTALmIEKpFrIJ1p4JW/5F3GUNu8j5snW/tOTJRTJ75MezuMiflIWcXn8P4zBH/Xm4KhIhrv9DuDsxGG2ZviEDY2qLsTAa996DoCzZlByJiDsoOMDcGHf2mq5/09CQufrtRfR2U6muilI8fx+gEA+5IErUAAAAASUVORK5CYII=";

var htmlFile16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAMAAAAMCGV4AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAbUExURUdwTBEA/////wAAAMDHyIeIjwcAq6ipUf7/AJzvhEIAAAABdFJOUwBA5thmAAAAWElEQVQI112OQQ4AIQgDaQXY/794BdEY5zalAUREbCML40LtcdpxgByTdAfgRDbSPb4K2lNJryC9pl2YHrpG7H6EA6qnHxiOex8079ruz2D/1y6mh/Jx8QMPvwJYhQJ+mAAAAABJRU5ErkJggg==";

var htmlFile32Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAMAAABEpIrGAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAbUExURUdwTAAA/////wAAAAAAgcHBwYGBgYGBAP//AMuYlv8AAAABdFJOUwBA5thmAAAApklEQVQ4y7XSQRLDIAwDQAuLkP+/uAyEAraZ9hIdo82AAZH/crlYkEwu/QWM8CDvwoO0iwDsIthkiwOomSpb0FvEAD1cxQIITBEAAvciHCBK7UkaMQDZ+vpFD2D0Vjyg9SDJZxELyl2wxQDXO5ALuE1nNllq/wVKkgwAlzHdEqB2cTioCkRHGR41IaI6fmcKwYX+gjSYot91Sscx4zf5AshhJtBDRD58+AgEB4pxSQAAAABJRU5ErkJggg==";

var internetExplorer16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAYUExURUdwTAcAqxEA/6ipUQAAAMDHyP7/AIeIj14ckmEAAAABdFJOUwBA5thmAAAAWklEQVQY002QURYAEAgEbbXc/8ZSif0y815LxngRz38OSoNkQQnn2eYw1BloEyyklbjcRmv+tujUONwMpeB7kE9oi+zQunEtqw6hAa/zCFopIPcixSJv0+8PNtfvAbX66OpXAAAAAElFTkSuQmCC";

var logOff24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABcAAAAYCAMAAAAmopZHAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAnUExURUdwTP///wAAAMDHyP7/AIeIj6ipUREA//8AAKoAVwCpU6lUqgD/AON30IcAAAABdFJOUwBA5thmAAAAoUlEQVQoz22QURKDIAxEyW4W1Pb+522CWgVd8sG8N8kQSrkilLfIiFdsb0JG4SlyyLY9RGLwy0nITMuqDT6K4FiXFe4O3oTMiA+aKmgjX4jWMOIiLtZCTDg4m4kzRoQKOOIKSWHIGdOtZtOADXJ3q+PHVHOITHFl5zkiO65g53Gh0/0folQjAQYmST8qeEd5+hZH5VIn7hue1cW80e0bZvwD+wkD6X08PtQAAAAASUVORK5CYII=";

var msDos16 = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAeUExURUdwTAAAAIeIj6oAV/8AAAcAq6ipUf7/ABEA/8DHyHxwNV4AAAABdFJOUwBA5thmAAAAcElEQVQY01WOAQ6AMAgDVwYw//9hS9FEm7CQWwusBdjqByx26rtMzAbYVEsABlMET0T/BNcbmbSMmr8pRAQyEw3cfcc5kUVlAxoOgEKbBBggrMaKXA24AoeGP0DVRLAdqASyZos7Td8tOqTvSCz8tW4gSwKSZc/r8wAAAABJRU5ErkJggg==";

var notepad16 = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAVUExURUdwTFOoqQD//wAAAMDHyIeIj////3W9FIoAAAABdFJOUwBA5thmAAAAUUlEQVQY04WPQRLAIAjEWED+/+TiIracmvFiJjIosrFGClsAzzGmjTkNFERRIoO6Z0CBfoAS3wkUI0gxgxQjiF1cvApu5pcpIv4K93X++06WBx6UAlwUWdTdAAAAAElFTkSuQmCC";

var notepadFile32Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAMAAABEpIrGAAAAD1BMVEVHcEz////AwMAAAACAgIAnu+Y7AAAAAXRSTlMAQObYZgAAAE1JREFUOMvlkYEGwEAMQ9O+/v83b2puWDC2m3FPUFIRIu2AkwYVZcXwCaMiuf1gyXcfaA6H6PtBwpySf+jAhTUTPthi9pqqdJy+BJb2NgG9BdieCff+AAAAAElFTkSuQmCC";

var outlook16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAkUExURUdwTAcAqxEA/////wAAAP7/AIeIjwD//1Ooqf8AAMDHyKoAV952bY0AAAABdFJOUwBA5thmAAAAbElEQVQY01WPSxLAIAhDCVjA9v73Lb/p2IcLicEJRIWbGR2wGaBfR+yG29GtKrM7dFikEgLkkjhRLTCk2FtSQFLP+ynHUEMywjUlp4Prr9OR6drR05JCOtaQcbFWx4XfEZcJ3zqIuPxbN5S+vbMbAw1pOdpkAAAAAElFTkSuQmCC";

var paint16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAnUExURUdwTP///wAAAMDHyIeIj1OoqaipUQcAq/8AAKoAV/7/ABEA/wD///UHVbMAAAABdFJOUwBA5thmAAAAX0lEQVQY06WOWxaAIAhEeVvZ/tfbIJr9N0cBLwNHopSJ4FBJvgDXLAOLKzIwaoTjFL8bBafNtEuBUBt7mvcEFlfMvc0T7LdtFTFlZoUWANHqr69Ny2sYYIz8cJBMZf0AaAwCYiqrjuQAAAAASUVORK5CYII=";

var paint32Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAMAAABEpIrGAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAtUExURUdwTP///wAAAMDHyIeIjwcAq1OoqalUqqoAV6ipUREA//8AAP8A/wD///7/AGyoo8cAAAABdFJOUwBA5thmAAAAxklEQVQ4y+2SWxaEIAxDJQ0g83D/yx1aABF0B1N/OM01iQe3bR6C2B7GNAKYtsMRK0A5iQJwiiCBftQIN3c4N3YaLVszqR6mBQZvbr0DED/RiJ17Br4KEJJXbB0qsb8bQACahpZciA7oCo6uR8Mb0YAkQrihrQ8vIwrAdJBwPgxfY0SMBUiHJNVffvjWQhhwq2ciT44Acv6dznWuN+bKiA31uRIKSJU7MQMnceewFMDy2wwe5f3pzmUouSb8HZ6ve3LYsEwVfidjCKM+vdabAAAAAElFTkSuQmCC";

var run24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAWCAMAAADto6y6AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAnUExURUdwTP///wAAAMDHyIeIjwcAq6oAV/8AAACpUxEA/6lUqgD//wD/AKlOo4wAAAABdFJOUwBA5thmAAAAhElEQVQoz4WQAQ6EIAwES1tPiv7/vdeloqFqHBONDGtxiYDeYAohmVMsg8K4HgR35PtTZcbFb8BZrCIrcGF9sYYgPvDXzaBqDaH+EFEIM59Vd8uiSWsIjISocCSm4TBjXVWPW/yHlrT/S2CI8r0SldJPlejHZQjKKNp/Eld25irxJZAjf6KnBJOwTu4+AAAAAElFTkSuQmCC";

var settings24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAMAAADXqc3KAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAVUExURUdwTP///6ipUQAAAMDHyP7/AIeIj+yok/YAAAABdFJOUwBA5thmAAAAqElEQVQoz3WQARKEMAgDC6H8/8kXgNaqHnUczZKADn8URpfbrW5gNcsLIMs+gLDsD7BvBwxir63CwcvT9xiu2ssRuG8gOgXwCAPA5/2BKlO0AHvmBRCkAHXdgH0i6Ch6GyiLue2QmBG7EdDNcznyjQBhkezLnWYIC+T0PnqA7ItNFQhvAQNU018pQTk8g0vX7I2c/cMCIKPrPg7Al5JwgpHmlnDoix7aD+ZQBgFqmFWKAAAAAElFTkSuQmCC";

var settingsPrinters16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAANCAMAAABBwMRzAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAYUExURUdwTP///wAAAMDHyP7/AIeIj/8AAAD/AB/J9zYAAAABdFJOUwBA5thmAAAATElEQVQI11WOCQ7AIAzDWrNs///xwjouIyEFp6gRoU5MdDUfndEPf025IZyroF78csVMfA9fcXjpudHytv6b6cGGts1DLUFtOyGCgxfglgJPKhCz0gAAAABJRU5ErkJggg==";

var shutDown24 = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAMAAADXqc3KAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAbUExURUdwTBEA/wAAAMDHyIeIjwcAq////wD///7/AD9rfX0AAAABdFJOUwBA5thmAAAAgklEQVQoz23R6xYFIQQF4Bhl3v+JDzHkaP/Ll6XLGBqSjB6iR9KIaD0Wsnz1pQnKVtt/IQHU1R8ZzFkIBXEDwEFSpIQgPVYB3mRHPoAVGGYD4LV7Lh0vww32jA5zgk2poBdVah2YlID6jBgUgP70QQ6Yv+XkUD7SqYPTDYzKhJO+8g96dQXmQ7dOfAAAAABJRU5ErkJggg==";

var windowsExplorer16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAMAAAAMCGV4AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAeUExURUdwTP///wAAAMDHyP7/AIeIjwD//xEA/6ipUQcAq/jryeYAAAABdFJOUwBA5thmAAAAXElEQVQI11WMWxLAIAgDeRil979wE6sdXT+YTUAzg7AftOTDrQzWGtwTCA6CoCe8e2AuyaU9Z/C5tEcdfbKv3TdIUbV6DV6PUaufPz+dgXyjgG6xURB2wOByrtoLU90C2k4z3ToAAAAASUVORK5CYII=";

var windowsUpdate16Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAOBAMAAADUAYG5AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAeUExURUdwTAAAABEA/wCpUwcAq/8AAMDHyFOoqf7/AAD//0xDm5cAAAABdFJOUwBA5thmAAAAYUlEQVQIHQXAsQ2CQAAF0McG91GCliCJ9aGNJdEFKFiBHSztbN3YoEkgstYC6dZbwbZ3ORTYMnxSGPd2+B4qxjan9llkT3KeKkn/66cK/eN9XaC9zNMCzTTfCzi+FqBJ8QfutQupHeo2VwAAAABJRU5ErkJggg==";

var windowsUpdate24Min = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAB8AAAAbCAMAAACz4aQdAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAkUExURUdwTAcAqxEA/wAAAAD/AACpU/8AAIeIj/////7/AMDHyAD//6qgZvEAAAABdFJOUwBA5thmAAAA60lEQVQoz33TWxaDIAwEUMhksNX977dJIIi0p+GDjzs8xVLuglXZC6v+SZg0QL8C6M3ZXYHDis8MVj9VScoc30amecjc1Vwy0bw1zEoW5O5aCxfg7Z2EitS+VRnzi/vb+5EIh7k1eTjVArVynDUWgwCxQHCVSir6+a2OdX8SrKcSeUNel1wCgL5CFRpz3q0heckoCp2V87IP4Us5DmagwYsbvzT9HHx7cLow+XZnzZv1Bbbx6hyBfvRtfOEcI1Vq/0rrW0mGszWQ4PqWcspgKzy5kCQJDI5E2QOoS+1PGcCq3y+93IFf+usv+QAnHQeZYIDm/wAAAABJRU5ErkJggg==";

var backMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAANAgMAAAALcNzSAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAJUExURUdwTP///wAAAObOYyIAAAABdFJOUwBA5thmAAAAL0lEQVQI12Ng4GAAAg0QMQOImSKABGfUqhUMqqGhEQxTQQSYBRYDy4LVQXQA9QIANjUJlHnyLzsAAAAASUVORK5CYII=";

var forwardMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAANAgMAAAALcNzSAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAJUExURUdwTP///wAAAObOYyIAAAABdFJOUwBA5thmAAAALklEQVQI12NgYGhgAIIFIGIGiJjGwLBq1dQGhqmhoQkgIgLCAouBZaHqwDoaGADPEQ5E4pHvWQAAAABJRU5ErkJggg==";

var cutMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAA8AAAAUCAMAAABlGZcgAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAPUExURUdwTP///wD//wAAAMDHyCof7LkAAAABdFJOUwBA5thmAAAAUElEQVQY011NQQKAMAjC6P9vbjEdOi8IIAIkcrQxzP+VUUJuNGeTHTz6uHNP9bY/wWbLa/YOdK4AMAMmKtOIPmtYsJCk+MH3wuHrkDAiezd+y2gBiL6j0y8AAAAASUVORK5CYII=";

var copyMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAAUCAMAAAC6V+0/AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAPUExURUdwTP///wAAABEA/wcAq0wNhg4AAAABdFJOUwBA5thmAAAAUElEQVQY062QQRIAEAzEqP7/zZRquzuOciITe9AkaIl0p9qUXV4y7TqrKi3Lzeqyl7jM5V6Ocizsue1SuS9Yev2hPBLKA5bxA7Wkv6LyIYEJq6sCIe6QxwMAAAAASUVORK5CYII=";

var deleteMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABIAAAASAQMAAABsABwUAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAGUExURUdwTP8AACGysLwAAAABdFJOUwBA5thmAAAAP0lEQVQIHQXAsQ2AIBAAwCOfYEN0A+MgxjiSpQUFYzAeI1BaGgOfpgZXZitEJ00M0iQ6S2HN7MGZqJoXj9vBD56pCfiqaaqOAAAAAElFTkSuQmCC";

var propertiesMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABIAAAATCAMAAACqTK3AAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAASUExURUdwTAcAq////wAAAMDHyBEA/z0bqTsAAAABdFJOUwBA5thmAAAASUlEQVQY083NiQ0AIAgDQATdf2VLBd8FLEbjhYBIxhg8S7R6WWtTahho9EPCnBSh0CzIf7TY4JSOm5syY8RBulEpOMxfXQ9dEen84AK0yn1z8gAAAABJRU5ErkJggg==";

var upDirMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAARAgMAAACgKmQtAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAMUExURUdwTAAAAMDHyP7/AN7skwoAAAABdFJOUwBA5thmAAAAP0lEQVQI12NgDA1gYGBg370FSMq9ewskQ0GAIe/dOyCvevfu3TsZ8p6B2VPB7NA8EHs7kjgye2to+E4UvWDTABuUMnUEzfu/AAAAAElFTkSuQmCC";

var viewsMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAARAgMAAACgKmQtAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAMUExURQcAq////wAAABEA/90dSWgAAAAvSURBVAjXY1gFAgz7/////48Bwp4aGhoaxjBFNEQUSLotcVvGMIU1hDWMTHGwmQA7biWnTn4uuAAAAABJRU5ErkJggg==";

var ieFavoritesMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAARCAMAAADqmnyMAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAASUExURUdwTAAAAMDHyP7/ABEA/////4twyGIAAAABdFJOUwBA5thmAAAARUlEQVQY042P2woAIAhDt1r//8uJQYgZteHLON4AgEuIYm9uFllMWQhsPZuhezuQOkm5MykpkxYNqw/yMrPafrnz/VGhCbAmAq8JUmWaAAAAAElFTkSuQmCC";

var ieHistoryMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAATCAMAAACnUt2HAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAASUExURUdwTP///6ipUQAAAMDHyIeIj3lKw6YAAAABdFJOUwBA5thmAAAAd0lEQVQY013QQRbEIAgDUCHx/lceCMho043+h1Rc6xtcSyUXhiEazBhuwJAlhlrVLzD3ikxNWFVj1fmtS1S/y9w31tvPvTCvYfqzSOdPJc075zjr++POPdpR2CNytC8PGaTA7jF5qoM25o1YswThek1GHnoeOfMDBO8C2buQ9XYAAAAASUVORK5CYII=";

var ieMailMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAB0AAAAUCAMAAABGQsb1AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAVUExURUdwTP///wAAABEA/wD///7/AIeIjyTvsQEAAAABdFJOUwBA5thmAAAAdElEQVQoz32S2xZAIQQFQ/n/Tz5FnOiyX6dhhYIpJQQh5EEbtJ2SZsC7254uEeLZVa8CXt0O68k1c8fmTuhYRzNdhys2F9lhZcNSWYYAjnltPV0wzBCpuh1L4iZQvzNcSXI1BgdOE+lv+N8j7/RxAV4/X88HgPEDB2A6UYcAAAAASUVORK5CYII=";

var ieHomeMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABMAAAAUBAMAAACdextHAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAPUExURUdwTP///wAAAP7/AP8AAEWttiwAAAABdFJOUwBA5thmAAAAUElEQVQI15XIsQ3AMAwDQUIb0BM41AbSBt5/qBiWkiJdvnocsDOYUPm0VWcZz3qkVuPlsRo5Uo2kRyM3z8big8U6SGrC6jjw2SG9m/F/1eEGR4kPgzD57nAAAAAASUVORK5CYII=";

var ieRefreshMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABEAAAATCAMAAABBexbDAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAMUExURUdwTP///wAAAACpU3sjm0cAAAABdFJOUwBA5thmAAAARUlEQVQY03XNUQ4AIAgC0JT737mZliqLzzeFpTXLopJxaiJKYnQF58u6niDuQmCpArqB93SRLjlXBFMwhdZzvPfw1l9mNiBTAbnPNW85AAAAAElFTkSuQmCC";

var iePrintMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAASCAMAAABsDg4iAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAYUExURUdwTP///wAAAMDHyBEA/wD/AACpU4eIj70DyucAAAABdFJOUwBA5thmAAAAVUlEQVQY06WQSxaAIAzEylTl/jemH5HKLMkyL5SCSIKFTNA+UNyVtMNw3lTD3qHYQ3f4bYhwVkIr7lxuqFKZ4ZKPEeervA2TsRHP9DXBI0mC/vd9+ADLTQLIaP/ViwAAAABJRU5ErkJggg==";

var ieSearchMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABQAAAAUCAMAAAC6V+0/AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAhUExURUdwTBEA/wD//wAAAAD/AACpU/////8AAFOoqYeIj8DHyGPWyQQAAAABdFJOUwBA5thmAAAAg0lEQVQY01WRSxLAIAjFlFh/9z9wBbTFxy4TYcCULHhSCDxFK2KKswfJRAaA5EPdI8suvOHFRKH2Kf7Sqy+qjnmx63EYUmWwTY2yumJUoc9GlNWJm3sXYzLpn7moKDvmpjanzkEnbM6Yc7FG2BMBoLXGf0zbJXci7dnqcsPl+eH1DekFZSwEdVF6IQIAAAAASUVORK5CYII=";

var ieStopMin = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABMAAAATCAMAAABFjsb+AAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAMUExURUdwTP////8AAAAAABJAN2UAAAABdFJOUwBA5thmAAAAS0lEQVQY043QAQoAIAgDQM3//7lUU7IRDQg6pGpEFvFQRWR4SreY3hR4kiMwI2bOdaGP6TYoTSGoLKfec+C8du/vm+F/YS+wv97zBL+ZAlrRDXzLAAAAAElFTkSuQmCC";

var classCallCheck$1 = function (instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
};

var createClass$1 = function () {
  function defineProperties(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i];
      descriptor.enumerable = descriptor.enumerable || false;
      descriptor.configurable = true;
      if ("value" in descriptor) descriptor.writable = true;
      Object.defineProperty(target, descriptor.key, descriptor);
    }
  }

  return function (Constructor, protoProps, staticProps) {
    if (protoProps) defineProperties(Constructor.prototype, protoProps);
    if (staticProps) defineProperties(Constructor, staticProps);
    return Constructor;
  };
}();

var defineProperty$1 = function (obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value: value,
      enumerable: true,
      configurable: true,
      writable: true
    });
  } else {
    obj[key] = value;
  }

  return obj;
};

var _extends$2 = Object.assign || function (target) {
  for (var i = 1; i < arguments.length; i++) {
    var source = arguments[i];

    for (var key in source) {
      if (Object.prototype.hasOwnProperty.call(source, key)) {
        target[key] = source[key];
      }
    }
  }

  return target;
};

var inherits$1 = function (subClass, superClass) {
  if (typeof superClass !== "function" && superClass !== null) {
    throw new TypeError("Super expression must either be null or a function, not " + typeof superClass);
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      enumerable: false,
      writable: true,
      configurable: true
    }
  });
  if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass;
};

var objectWithoutProperties$1 = function (obj, keys) {
  var target = {};

  for (var i in obj) {
    if (keys.indexOf(i) >= 0) continue;
    if (!Object.prototype.hasOwnProperty.call(obj, i)) continue;
    target[i] = obj[i];
  }

  return target;
};

var possibleConstructorReturn$1 = function (self, call) {
  if (!self) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return call && (typeof call === "object" || typeof call === "function") ? call : self;
};

var toConsumableArray = function (arr) {
  if (Array.isArray(arr)) {
    for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) arr2[i] = arr[i];

    return arr2;
  } else {
    return Array.from(arr);
  }
};

var SettingsContext = React.createContext();

var toggle = function toggle(dis, key) {
  return function () {
    dis.setState(function (state) {
      return defineProperty$1({}, key, !state[key]);
    });
  };
};

var setKeyValue = function setKeyValue(dis, key) {
  return function (val) {
    dis.setState(function (state) {
      return defineProperty$1({}, key, val);
    });
  };
};

var SettingsProvider = function (_Component) {
  inherits$1(SettingsProvider, _Component);

  function SettingsProvider() {
    var _ref3;

    var _temp, _this, _ret;

    classCallCheck$1(this, SettingsProvider);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref3 = SettingsProvider.__proto__ || Object.getPrototypeOf(SettingsProvider)).call.apply(_ref3, [this].concat(args))), _this), _this.state = {
      scale: 1,
      crt: true,
      fullScreen: false,
      isMobile: false,
      bgImg: window && window.localStorage.getItem("bgImg"),
      bgStyle: window && window.localStorage.getItem("bgStyle")
    }, _this.toggleCrt = toggle(_this, "crt"), _this.toggleFullScreen = toggle(_this, "fullScreen"), _this.toggleMobile = toggle(_this, "isMobile"), _this.changeScale = setKeyValue(_this, "scale"), _this.updateLocalStorage = function (key, val) {
      if (window && window.localStorage) {
        window.localStorage.setItem(key, val);
        if (val) {
          _this.setState(defineProperty$1({}, key, val));
        }
      }
    }, _this.removeLocalStorage = function (key) {
      var keys = key;
      if (!Array.isArray(key)) {
        keys = [key];
      }
      if (keys.length < 1) {
        return;
      }
      if (window && window.localStorage) {
        keys.map(function (k) {
          return window.localStorage.removeItem(k);
        });

        _this.setState(keys.reduce(function (acc, val) {
          return _extends$2({}, acc, defineProperty$1({}, val, null));
        }, {}));
      }
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(SettingsProvider, [{
    key: "render",
    value: function render() {
      var changeScale = this.changeScale,
          toggleCrt = this.toggleCrt,
          toggleFullScreen = this.toggleFullScreen,
          toggleMobile = this.toggleMobile,
          updateLocalStorage = this.updateLocalStorage,
          removeLocalStorage = this.removeLocalStorage;

      var context = _extends$2({}, this.state, {
        changeScale: changeScale,
        toggleCrt: toggleCrt,
        toggleFullScreen: toggleFullScreen,
        toggleMobile: toggleMobile,
        updateLocalStorage: updateLocalStorage,
        removeLocalStorage: removeLocalStorage
      });
      return React__default.createElement(
        SettingsContext.Provider,
        { value: context },
        this.props.children
      );
    }
  }]);
  return SettingsProvider;
}(React.Component);

function styleInject$1(css, ref) {
  if ( ref === void 0 ) ref = {};
  var insertAt = ref.insertAt;

  if (!css || typeof document === 'undefined') { return; }

  var head = document.head || document.getElementsByTagName('head')[0];
  var style = document.createElement('style');
  style.type = 'text/css';

  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }

  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

var css$s = "._window_react-draggable__27nui {\n  position: absolute;\n  top: 0px;\n  left: 0px;\n  z-index: 7;\n  /* transition: 500ms height ease-in, 500ms width ease-in; */ }\n  ._window_react-draggable__27nui._window_react-draggable-maximized-hack__3pIWN {\n    height: calc(100% - 29px) !important;\n    width: calc(100% - 2px) !important; }\n  ._window_react-draggable__27nui ._window_react-resizable-handle__Djg7E {\n    height: 15px;\n    width: 15px;\n    z-index: 1;\n    position: absolute;\n    right: -3px;\n    bottom: -3px; }\n\n._window_react-draggable-dragging__3DdMI ._window_IframeWindow__1D6wk > div,\n._window_react-draggable-dragging__3DdMI ._window_IframeWindow__1D6wk iframe,\n._window_react-draggable-dragging__3DdMI ._window_IframeWindow__1D6wk ._window_pointerIssues__249vE {\n  pointer-events: none; }\n\n._window_react-draggable-dragging__3DdMI iframe {\n  pointer-events: none; }\n\n._window_Window__YEep_ {\n  height: 100%;\n  width: 100%; }\n  ._window_Window__YEep_._window_Window--maximized__cFO3_ {\n    width: calc(100% + 4px);\n    height: calc(100% + 4px); }\n  ._window_Window__YEep_:not(._window_Window--active__1lGvN) {\n    filter: grayscale(100%); }\n";
var styles = { "react-draggable": "_window_react-draggable__27nui", "react-draggable-maximized-hack": "_window_react-draggable-maximized-hack__3pIWN", "react-resizable-handle": "_window_react-resizable-handle__Djg7E", "react-draggable-dragging": "_window_react-draggable-dragging__3DdMI", "IframeWindow": "_window_IframeWindow__1D6wk", "pointerIssues": "_window_pointerIssues__249vE", "Window": "_window_Window__YEep_", "Window--maximized": "_window_Window--maximized__cFO3_", "Window--active": "_window_Window--active__1lGvN" };
styleInject$1(css$s);

var resizeStyles = function resizeStyles(pixels) {
  var corners = pixels * 4;
  return {
    bottom: { height: pixels, bottom: -pixels },
    bottomLeft: { height: corners, width: corners, left: -pixels },
    bottomRight: {
      height: corners,
      width: corners,
      right: -pixels * 2,
      bottom: -pixels * 2
    },
    left: { width: pixels, right: -pixels },
    right: { width: pixels, marginLeft: "100%" },
    top: { height: pixels },
    topLeft: { height: corners, width: corners, left: -pixels, top: -pixels },
    topRight: { width: 0, height: 0 }
  };
};

var getMaxes = function getMaxes(document) {
  var holder = document.querySelector(".w98");

  if (holder && (holder.offsetWidth < 640 || holder.offsetHeight < 480)) {
    return {
      maxWidth: Math.ceil(holder.offsetWidth - 5),
      maxHeight: Math.ceil(holder.offsetHeight - 32)
    };
  }

  return {};
};

var randomizeLaunchSpot = function randomizeLaunchSpot(max) {
  return Math.ceil(Math.random() * max);
};

var launchPositions = function launchPositions(propX, propY, isMobile) {
  var random = randomizeLaunchSpot(80);
  var x = propX || random;
  var y = propY || random;
  return !isMobile ? {
    x: x,
    y: y
  } : {
    x: x / 2,
    y: y / 2
  };
};

var Window = function (_React$PureComponent) {
  inherits$1(Window, _React$PureComponent);

  function Window() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, Window);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = Window.__proto__ || Object.getPrototypeOf(Window)).call.apply(_ref, [this].concat(args))), _this), _this.state = _extends$2({
      height: _this.props.initialHeight,
      width: _this.props.initialWidth,
      maximized: _this.context.isMobile && _this.props.resizable || _this.props.maximizeOnOpen
    }, launchPositions(_this.props.inintalX, _this.props.initialY)), _this.updateLocation = function (a, b) {
      return _this.setState({ x: b.x, y: b.y, isDragging: false });
    }, _this.resize = function (e, direction, ref, delta, position) {
      return _this.setState(_extends$2({
        width: ref.style.width,
        height: ref.style.height
      }, position));
    }, _this.maximize = function () {
      return _this.setState({ maximized: true });
    }, _this.restore = function () {
      return _this.setState({ maximized: false });
    }, _this.toggleDrag = function (val) {
      return function () {
        return _this.setState({ isDragging: val });
      };
    }, _this.toggleResize = function (val) {
      return function () {
        return _this.setState({ isResizing: val });
      };
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(Window, [{
    key: "render",
    value: function render() {
      var _this2 = this,
          _cx2;

      var context = this.context,
          props = this.props;

      var resizeProps = this.props.resizable && !this.state.maximized ? {
        resizeHandleStyles: resizeStyles(4),
        onResize: this.resize,
        onResizeStart: this.toggleResize(true),
        onResizeStop: this.toggleResize(false)
      } : { resizeHandleStyles: resizeStyles(0) };

      var maximizedProps = this.state.maximized ? {
        size: { width: "100%" },
        position: { x: -2, y: -3 },
        disableDragging: true
      } : undefined;
      return React__default.createElement(
        React__default.Fragment,
        null,
        this.state.isDragging && React__default.createElement(
          reactRnd.Rnd,
          {
            size: { width: this.state.width, height: this.state.height },
            position: { x: this.state.x, y: this.state.y },
            scale: context.scale,
            className: styles["react-draggable"]
          },
          React__default.createElement(props.Component, _extends$2({}, props, this.state, {
            isDragging: false,
            className: cx(props.className, styles.Window, styles["Window--active"])
          }))
        ),
        React__default.createElement(
          reactRnd.Rnd,
          _extends$2({
            className: cx(styles["react-draggable"], defineProperty$1({}, styles["react-draggable-maximized-hack"], this.state.maximized)),
            size: !this.state.maximized && {
              width: this.state.width,
              height: this.state.height
            },
            position: { x: this.state.x, y: this.state.y },
            dragHandleClassName: "Window__title",
            onDragStart: this.toggleDrag(true),
            onDragStop: !this.state.maximized && this.updateLocation,
            bounds: ".w98",
            minWidth: this.props.minWidth,
            minHeight: this.props.minHeight,
            maxWidth: !this.state.maximized ? this.props.maxWidth : "105%",
            maxHeight: !this.state.maximized ? this.props.maxHeigh : "105%",
            scale: context.scale,
            onMouseDown: this.props.moveToTop ? function () {
              return _this2.props.moveToTop(_this2.props.id);
            } : undefined
          }, resizeProps, maximizedProps, getMaxes(document)),
          React__default.createElement(
            props.Component,
            {
              title: props.title,
              icon: props.icon,
              footer: props.footer,
              onOpen: props.multiWindow && function () {
                return props.onOpen(props.id);
              },
              onClose: function onClose() {
                return props.onClose(props.id);
              },
              onMinimize: props.onMinimize && function () {
                return props.onMinimize(props.id);
              },
              onRestore: props.resizable && this.restore,
              onMaximize: props.resizable && this.maximize,
              changingState: this.state.isDragging || this.state.isResizing,
              maximizeOnOpen: this.context.isMobile || this.props.maximizeOnOpen,
              className: cx(props.className, styles.Window, (_cx2 = {}, defineProperty$1(_cx2, styles["Window--active"], props.isActive), defineProperty$1(_cx2, styles["react-draggable-dragging"], this.state.isDragging), _cx2)),
              resizable: props.resizable,
              menuOptions: props.menuOptions,
              hasMenu: props.hasMenu,
              explorerOptions: props.explorerOptions,
              data: props.data,
              style: props.style
            },
            props.children
          )
        )
      );
    }
  }]);
  return Window;
}(React__default.PureComponent);

Window.contextType = SettingsContext;


Window.defaultProps = {
  minWidth: 200,
  minHeight: 200,
  initialWidth: 250,
  initialHeight: 250,
  // maxHeight: 448,
  // maxWidth: 635,
  resizable: true,

  scale: 1,
  title: "Needs default"
};

var buildMenu = function buildMenu(props) {
  return [{
    title: "File",
    options: [{ title: "Open", isDisabled: true }, { title: "Close", onClick: function onClick() {
        return props.onClose(props.id);
      } }]
  }, {
    title: "Help",
    options: [{ title: "About " + props.title, isDisabled: true }]
  }];
};
var noop = function noop() {};

var Explorer = function Explorer(props) {
  return React__default.createElement(Window, _extends$2({}, props, {
    Component: WindowExplorer,
    explorerOptions: [{
      icon: backMin,
      title: "Back",
      onClick: noop
    }, {
      icon: forwardMin,
      title: "Forward",
      onClick: noop
    }, {
      icon: upDirMin,
      title: "Up",
      onClick: noop
    }, {
      icon: cutMin,
      title: "Cut",
      onClick: noop
    }, {
      icon: copyMin,
      title: "Copy",
      onClick: noop
    }, {
      icon: deleteMin,
      title: "Delete",
      onClick: noop
    }, {
      icon: propertiesMin,
      title: "Properties",
      onClick: noop
    }, {
      icon: viewsMin,
      title: "Views"
    }],
    menuOptions: buildMenu(props)
  }));
};

var css$t = "._styles_IframeWindow__1vVpi > div:not(:first-child),\n._styles_IframeWindow__1vVpi iframe {\n  width: 100%;\n  flex-grow: 1; }\n\n._styles_IframeWindow__1vVpi iframe {\n  height: 100%; }\n\n._styles_IframeWindow--alert__2XtrD._styles_WindowAlert__1yOyl {\n  position: absolute;\n  left: 50%;\n  top: 50%;\n  -ms-transform: translateX(-50%) translateY(-50%);\n  -webkit-transform: translateX(-50%) translateY(-50%);\n  -moz-transform: translateX(-50%) translateY(-50%);\n  -o-transform: translateX(-50%) translateY(-50%);\n  transform: translateX(-50%) translateY(-50%);\n  z-index: 8; }\n";
var styles$1 = { "IframeWindow": "_styles_IframeWindow__1vVpi", "IframeWindow--alert": "_styles_IframeWindow--alert__2XtrD", "WindowAlert": "_styles_WindowAlert__1yOyl" };
styleInject$1(css$t);

var IFrame = function (_Component) {
  inherits$1(IFrame, _Component);

  function IFrame() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, IFrame);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = IFrame.__proto__ || Object.getPrototypeOf(IFrame)).call.apply(_ref, [this].concat(args))), _this), _this.state = {
      displayAlert: _this.props.data.displayAlert || true
    }, _this.confirm = function () {
      return _this.setState({ displayAlert: false });
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(IFrame, [{
    key: "render",
    value: function render() {
      var props = this.props,
          state = this.state;


      var commonProps = {
        title: props.title,
        icon: props.icon,
        onClose: function onClose() {
          return props.onClose(props.id);
        }
      };

      if (state.displayAlert) {
        return React__default.createElement(
          WindowAlert,
          _extends$2({}, commonProps, {
            onOK: this.confirm,
            onCancel: commonProps.onClose,
            className: styles$1["IframeWindow--alert"]
          }),
          props.data.disclaimer || "The Following is an iframe displaying, content belongs to the original creator at " + props.data.src
        );
      }

      return React__default.createElement(
        Window,
        _extends$2({}, props, {
          className: styles$1.IframeWindow,
          initialHeight: props.data.height || 380,
          initialWidth: props.data.width || 440,
          menuOptions: props.data.useMenu && buildMenu(props),
          Component: WindowProgram,
          resizable: !(props.data.width || props.data.height)
        }),
        React__default.createElement(
          "div",
          { style: props.data && props.data.style },
          React__default.createElement("iframe", { src: props.data.src, title: props.title })
        )
      );
    }
  }]);
  return IFrame;
}(React.Component);

var css$u = "@font-face {\n  font-family: \"FixedSys\";\n  src: url(\"../../assets/FixedsysStripped.woff2\") format(\"woff2\"); }\n\n._styles_Notepad__textarea__7hcBI {\n  box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c;\n  padding: 4px 2px;\n  overflow: hidden;\n  background-color: white;\n  display: flex;\n  flex-grow: 1;\n  margin-bottom: 2px; }\n\n._styles_Notepad__2Wp4k textarea {\n  font-family: \"FixedSys\", \"Courier New\", Courier, monospace;\n  resize: none;\n  white-space: nowrap;\n  outline: none;\n  min-height: 100%;\n  border: none;\n  flex-grow: 1; }\n\n._styles_Notepad--wrap__EDVDa textarea {\n  width: 100%;\n  white-space: normal; }\n";
var styles$2 = { "Notepad__textarea": "_styles_Notepad__textarea__7hcBI", "Notepad": "_styles_Notepad__2Wp4k", "Notepad--wrap": "_styles_Notepad--wrap__EDVDa" };
styleInject$1(css$u);

var buildMenu$1 = function buildMenu(props, state) {
  return [{
    title: "File",
    options: [{
      title: "New",
      isDisabled: !props.multiWindow && !props.onOpen,
      onClick: function onClick() {
        return props.onOpen(props.id);
      }
    }, {
      title: "Open",
      isDisabled: true,
      onClick: function onClick() {
        return props.onOpen(props.id);
      }
    }, { title: "Close", onClick: function onClick() {
        return props.onClose(props.id);
      } }, {
      title: "Wrap",
      onClick: function onClick() {
        return state.toggleWrap(!state.wrap);
      },
      isChecked: state.wrap
    }]
  }, {
    title: "Help",
    options: [{ title: "About " + props.title, isDisabled: true }]
  }];
};

var Notepad = function (_React$Component) {
  inherits$1(Notepad, _React$Component);

  function Notepad() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, Notepad);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = Notepad.__proto__ || Object.getPrototypeOf(Notepad)).call.apply(_ref, [this].concat(args))), _this), _this.state = _this.props.data ? {
      text: _this.props.data.content,
      wrap: _this.props.data.wrap
    } : {}, _this.toggleWrap = function (val) {
      return _this.setState({ wrap: val });
    }, _this.setText = function (text) {
      return _this.setState({ text: text });
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(Notepad, [{
    key: "render",
    value: function render() {
      var props = this.props,
          toggleWrap = this.toggleWrap,
          setText = this.setText;
      var _state = this.state,
          wrap = _state.wrap,
          text = _state.text;

      return React__default.createElement(
        Window,
        _extends$2({}, props, {
          icon: notepad16,
          footer: [{ text: "needs 100% width height" }, { text: "overflow control" }],
          menuOptions: buildMenu$1(props, { toggleWrap: toggleWrap, wrap: wrap }),
          className: cx(styles$2.Notepad, props.className, {
            "Notepad--wrap": wrap
          }),
          title: (props.title !== "Notepad" ? props.title : "Untitled") + " - Notepad",
          Component: WindowProgram
        }),
        React__default.createElement(
          "div",
          { className: styles$2.Notepad__textarea },
          React__default.createElement(
            "textarea",
            { onChange: function onChange(e) {
                return setText(e.target.value);
              } },
            text
          )
        )
      );
    }
  }]);
  return Notepad;
}(React__default.Component);

Notepad.defaultProps = {
  data: {
    content: ""
  }
};

var css$v = "@font-face {\n   {\n    font-family: pixelmix;\n    src: url(\"../../assets/pixelmix.woff2\") format(\"woff2\");\n    font-weight: normal; } }\n\n@font-face {\n   {\n    font-family: FixedSys;\n    src: url(\"../../assets/FixedsysStripped.woff2\") format(\"woff2\"); } }\n\n._styles_JSDos__x2ZCc input {\n  filter: opacity(0%);\n  position: absolute;\n  left: -2000px; }\n\n._styles_JSDos__x2ZCc ._styles_terminal__19JQ4 {\n  box-shadow: inset -1px -1px 0px #ffffff, inset 1px 1px 0px 0px #808088, inset -2px -2px 0px #bbc3c4, inset 2px 2px 0px 0px #0c0c0c;\n  flex-grow: 1;\n  background-color: black;\n  color: white;\n  font-size: 8px;\n  letter-spacing: 1px;\n  line-height: 1.5em;\n  padding: 8px 4px; }\n  ._styles_JSDos__x2ZCc ._styles_terminal__19JQ4 * {\n    font-family: pixelmix, FixedSys, MSSansSerif, \"Courier New\", Courier, monospace; }\n  ._styles_JSDos__x2ZCc ._styles_terminal__19JQ4::selection {\n    background-color: white;\n    color: black; }\n\n._styles_JSDos__x2ZCc form:focus-within + ._styles_terminal__19JQ4 ._styles_terminal__content__1Nh9u > span:after {\n  content: \"_\"; }\n";
var styles$3 = { "JSDos": "_styles_JSDos__x2ZCc", "terminal": "_styles_terminal__19JQ4", "terminal__content": "_styles_terminal__content__1Nh9u" };
styleInject$1(css$v);

var buildMenu$2 = function buildMenu(props) {
  return [{
    title: "File",
    options: [{ title: "Open", isDisabled: true }, { title: "Close", onClick: function onClick() {
        return props.onClose(props.id);
      } }]
  }, {
    title: "Help",
    options: [{ title: "About " + props.title, isDisabled: true }]
  }];
};

var lineStart = "C:\\WINDOWNS>";

var JSDos = function (_Component) {
  inherits$1(JSDos, _Component);

  function JSDos() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, JSDos);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = JSDos.__proto__ || Object.getPrototypeOf(JSDos)).call.apply(_ref, [this].concat(args))), _this), _this.state = {
      value: "",
      content: []
    }, _this.input = React__default.createRef(), _this.focusInput = function () {
      _this.input.current.focus();
    }, _this.onInputBlur = function () {
      console.log("of");
    }, _this.onInputChange = function (e) {
      _this.setState({ value: e.target.value });
    }, _this.processEntry = function (e) {
      e.preventDefault();
      var response = void 0;
      try {
        response = safeEval(_this.state.value) || "Err... if nothing happened then maybe check your console?";
      } catch (e) {
        if (_this.state.content.length % 3) {
          response = "Maybe try some JavaScript?";
        } else {
          response = "Invalid command entered";
        }
      }
      _this.setState(function (state) {
        return {
          value: "",
          content: [].concat(toConsumableArray(state.content), [lineStart + state.value, response]).filter(function (entry) {
            return entry;
          })
        };
      });
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(JSDos, [{
    key: "render",
    value: function render() {
      var props = this.props;

      return React__default.createElement(
        Window,
        _extends$2({}, props, {
          title: "JS DOS Prompt",
          icon: msDos16,
          menuOptions: buildMenu$2(props),
          Component: WindowProgram,
          initialHeight: 200,
          initialWidth: 400,
          className: cx(styles$3.JSDos, props.className)
        }),
        React__default.createElement(
          "form",
          { name: "hiddenForm", onSubmit: this.processEntry },
          React__default.createElement("input", {
            type: "text",
            value: this.state.value,
            ref: this.input,
            onChange: this.onInputChange,
            onBlur: this.onInputBlur
          })
        ),
        React__default.createElement(
          "div",
          { className: styles$3.terminal, onClick: this.focusInput },
          React__default.createElement(
            "div",
            null,
            "Microsoft(R) Windows 98 "
          ),
          React__default.createElement(
            "div",
            { style: { marginLeft: "12px", marginBottom: "6px" } },
            "(C)Copyright Microsoft Corp 1981-1999."
          ),
          React__default.createElement(
            "div",
            { className: styles$3.terminal__content },
            this.state.content.map(function (entry) {
              return React__default.createElement(
                "div",
                null,
                entry
              );
            }),
            lineStart,
            React__default.createElement(
              "span",
              null,
              this.state.value
            )
          )
        )
      );
    }
  }]);
  return JSDos;
}(React.Component);

var css$w = "._styles_InternetExplorer__1Zwyh ._styles_WindowExplorer__view__2-Nq- {\n  position: relative;\n  overflow: scroll; }\n\n._styles_InternetExplorer__1Zwyh iframe._styles_crossOrigin__2hnzd {\n  width: 200%;\n  height: 200%;\n  transform: scale(0.5);\n  left: -50%;\n  top: -50%;\n  position: absolute; }\n";
styleInject$1(css$w);

var noop$1 = function noop() {};

var buildMenu$3 = function buildMenu(props) {
  return [{
    title: "File",
    options: [{ title: "Open", isDisabled: true }, { title: "Close", onClick: function onClick() {
        return props.onClose(props.id);
      } }]
  }, {
    title: "Help",
    options: [{ title: "About " + props.title, isDisabled: true }]
  }];
};

var canAccessIframe = function canAccessIframe(id) {
  var iframe = document && document.querySelector("." + id);
  var canAccess = iframe && iframe.contentDocument && iframe.contentDocument.body && iframe.contentDocument.body.scrollHeight;
  if (canAccess) {
    return {
      height: iframe.contentDocument.body.scrollHeight,
      width: iframe.contentDocument.body.scrollWidth
    };
  }
};

var InternetExplorer = function (_Component) {
  inherits$1(InternetExplorer, _Component);

  function InternetExplorer() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, InternetExplorer);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = InternetExplorer.__proto__ || Object.getPrototypeOf(InternetExplorer)).call.apply(_ref, [this].concat(args))), _this), _this.id = "b".concat(nanoid()).replace("-", ""), _this.state = {}, _this.getIframeDimension = function () {
      var iframeDimensions = canAccessIframe(_this.id);
      if (iframeDimensions && iframeDimensions !== _this.state.dimensions) {
        _this.setState({ dimensions: iframeDimensions });
      }
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(InternetExplorer, [{
    key: "componentDidMount",
    value: function componentDidMount() {
      var desktop = document.querySelector(".desktop");
      this.setState({
        dimensions: {
          height: desktop.innerHeight > 640 ? desktop.innerHeight : 640,
          width: desktop.innerWidth > 640 ? desktop.innerWidth : 640
        }
      });
      setTimeout(this.getIframeDimension, 3000);
    }
  }, {
    key: "render",
    value: function render() {
      var props = this.props;

      return React__default.createElement(
        Window,
        _extends$2({}, props, {
          Component: WindowExplorer,
          className: cx("InternetExplorer", props.className),
          title: (props.data.title || props.title !== "Internet Explorer" ? (props.data.title || props.title) + " - " : "") + "Internet Explorer",
          menuOptions: buildMenu$3(props),
          minHeight: 300,
          minWidth: 300,
          explorerOptions: [{
            icon: backMin,
            title: "Back",
            onClick: noop$1
          }, {
            icon: forwardMin,
            title: "Forward",
            onClick: noop$1
          }, {
            icon: ieStopMin,
            title: "Stop",
            onClick: noop$1
          }, {
            icon: ieRefreshMin,
            title: "Refresh",
            onClick: noop$1
          }, {
            icon: ieHomeMin,
            title: "Home",
            onClick: noop$1
          }, [{
            icon: ieSearchMin,
            title: "Search",
            onClick: noop$1
          }, {
            icon: ieFavoritesMin,
            title: "Favorites",
            onClick: noop$1
          }, {
            icon: ieHistoryMin,
            title: "History",
            onClick: noop$1
          }], {
            icon: ieMailMin,
            title: "Mail",
            onClick: noop$1
          }, {
            icon: iePrintMin,
            title: "Print",
            onClick: noop$1
          }],
          maximizeOnOpen: true
        }),
        props.data.__html && React__default.createElement("div", { dangerouslySetInnerHTML: props.data }),
        props.children,
        props.data && !props.data.html && props.data.src && (this.state.dimensions ? React__default.createElement(
          "div",
          { style: _extends$2({}, this.state.dimensions) },
          React__default.createElement("iframe", _extends$2({
            className: this.id,
            frameBorder: "0",
            src: props.data.src,
            title: props.data.src,
            importance: "low",
            height: "480",
            width: "640"
          }, this.state.dimensions))
        ) : React__default.createElement("iframe", {
          className: cx(this.id, "crossOrigin"),
          scrolling: "no",
          frameBorder: "0",
          src: "http://localhost:3000/" || props.data.src,
          title: props.data.src,
          importance: "low",
          height: "480",
          width: "640"
        }))
      );
    }
  }]);
  return InternetExplorer;
}(React.Component);

var google1999 = "<body bgcolor=\"#FFFFFF\" text=\"#000000\" link=\"#000099\" vlink=\"#003366\" alink=\"#000099\"><!-- BEGIN WAYBACK TOOLBAR INSERT -->\n<script type=\"text/javascript\" src=\"/static/js/timestamp.js?v=1553621510\" charset=\"utf-8\"></script>\n<script type=\"text/javascript\" src=\"/static/js/graph-calc.js?v=1553621510\" charset=\"utf-8\"></script>\n<script type=\"text/javascript\" src=\"/static/js/auto-complete.js?v=1553621510\" charset=\"utf-8\"></script>\n<script type=\"text/javascript\" src=\"/static/js/toolbar.js?v=1553621510\" charset=\"utf-8\"></script>\n<style type=\"text/css\">\nbody {\n  margin-top:0 !important;\n  padding-top:0 !important;\n  /*min-width:800px !important;*/\n}\n.wb-autocomplete-suggestions {\n    text-align: left; cursor: default; border: 1px solid #ccc; border-top: 0; background: #fff; box-shadow: -1px 1px 3px rgba(0,0,0,.1);\n    position: absolute; display: none; z-index: 2147483647; max-height: 254px; overflow: hidden; overflow-y: auto; box-sizing: border-box;\n}\n.wb-autocomplete-suggestion { position: relative; padding: 0 .6em; line-height: 23px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 1.02em; color: #333; }\n.wb-autocomplete-suggestion b { font-weight: bold; }\n.wb-autocomplete-suggestion.selected { background: #f0f0f0; }\n</style>\n<script type=\"text/javascript\">\n__wm.bt(600,27,25,2,\"web\",\"http://www13.google.com/\",\"1999-11-29\",1996,\"/static/\");\n</script><div class=\"wb-autocomplete-suggestions \" style=\"left: 167px; top: 23px; width: 684px;\"></div>\n<!-- END WAYBACK TOOLBAR INSERT -->\n\n<center>\n<img src=\"https://web.archive.org/web/19991129021746im_/http://www.google.com/images/Title_HomPg.gif\" width=\"600\" height=\"130\" border=\"0\" usemap=\"#map1\" alt=\"Google\">\n<map name=\"map1\">\n<area shape=\"RECT\" coords=\"493,58,595,103\" href=\"about.html\" alt=\"About Google\">\n<area shape=\"RECT\" coords=\"381,55,490,108\" href=\"jobs.html\" alt=\"Google Jobs\">\n</map>\n</center>\n\n<table width=\"95%\" border=\"0\"><tbody><tr><td>\n<center>\n<form action=\"/web/19991129021746/http://www.google.com/search\" method=\"get\" name=\"f\">\nSearch the web using Google<br>\n<input type=\"text\" value=\"\" framewidth=\"4\" name=\"q\" size=\"40\"><br>\n<nobr><input type=\"submit\" value=\"Google Search\">\n<input name=\"sa\" type=\"submit\" value=\"I'm feeling lucky\"></nobr><br>\n</form>\n</center>\n</td></tr></tbody></table>\n\n<script language=\"JavaScript\">\n<!--\ndocument.f.q.focus();\n// -->\n</script>\n<center>\n<p><font face=\"arial,geneva,helvetica\"><a href=\"pressrel/pressrelease6.html\">\nGoogle Wins PC Magazine's Technical Excellence Award<br>\nfor Innovation in Web Application Development</a></font></p></center>\n\n\n<center>\n<p><font face=\"arial,geneva,helvetica\"><font size=\"-2\">\xA91999 Google\nInc.</font></font></p></center>\n\n\n\n<!--\n     FILE ARCHIVED ON 02:17:46 Nov 29, 1999 AND RETRIEVED FROM THE\n     INTERNET ARCHIVE ON 23:12:26 Apr 11, 2019.\n     JAVASCRIPT APPENDED BY WAYBACK MACHINE, COPYRIGHT INTERNET ARCHIVE.\n\n     ALL OTHER CONTENT MAY ALSO BE PROTECTED BY COPYRIGHT (17 U.S.C.\n     SECTION 108(a)(3)).\n-->\n<!--\nplayback timings (ms):\n  LoadShardBlock: 425.475 (24)\n  esindex: 0.05 (7)\n  CDXLines.iter: 352.106 (12)\n  PetaboxLoader3.datanode: 223.92 (25)\n  exclusion.robots: 1.716 (7)\n  exclusion.robots.policy: 1.62 (7)\n  RedisCDXSource: 18.612 (7)\n  PetaboxLoader3.resolve: 114.583\n  load_resource: 145.987\n--></body>";

var accessories = [{ title: "Entertainment", icon: folderProgram16Min, options: [] }, { title: "Internet Tools", icon: folderProgram16Min, options: [] }, { title: "System Tools", icon: folderProgram16Min, options: [] }, { title: "Calculator", icon: calculator16Min, isDisabled: true }, {
  title: "Notepad",
  icon: notepad16,
  Component: Notepad,
  multiWindow: true
}, {
  title: "Paint",
  icon: paint16Min,
  Component: IFrame,
  data: { src: "https://jspaint.app/" },
  multiWindow: true
}, {
  title: "SkiFree",
  icon: folderProgram16Min,
  Component: IFrame,
  data: { src: "https://basicallydan.github.io/skifree.js/" },
  multiWindow: true
  // {
  //   title: "Minesweeper",
  //   icon: icons.folderProgram16,
  //   Component: IframeWindow,
  //   data: { src: "https://mines.now.sh/", height: 200, width: 150 },
  //   multiWindow: true
  // }
}];

var programs = [{ title: "Accessories", icon: folderProgram16Min, options: accessories }, { title: "Online Services", icon: folderProgram16Min, options: [] }, { title: "StartUp", icon: folderProgram16Min, options: [] }, {
  title: "InternetExplorer(BROKEN)",
  icon: internetExplorer16Min,
  Component: InternetExplorer,
  data: { __html: google1999 }
}, {
  title: "JS-DOS Prompt",
  icon: msDos16,
  Component: JSDos,
  multiWindow: true
}, { title: "Outlook Express", icon: outlook16Min, isDisabled: true }, { title: "Windows Explorer", icon: windowsExplorer16Min, isDisabled: true }];

var favorites = [{
  title: "Channels",
  options: [],
  icon: folder16Min
}, {
  title: "Links",
  icon: folder16Min,
  options: [{
    title: "MySpace",
    type: "ExternalLink",
    icon: htmlFile16Min,
    onClick: function onClick() {
      if (window.confirm("This will open a new tab, is that okay?")) {
        window.open("https://web.archive.org/web/20080320075546/www.myspace.com/my_address");
      }
    }
  }]
}, {
  title: "Media",
  icon: folder16Min,
  options: [{
    title: "My Big List of Films",
    type: "ExternalLink",
    icon: htmlFile16Min,
    onClick: function onClick() {
      if (window.confirm("This will open a new tab, is that okay?")) {
        window.open("https://letterboxd.com/padraig");
      }
    }
  }]
}, {
  title: "My Github",
  type: "ExternalLink",
  icon: htmlFile16Min,
  onClick: function onClick() {
    if (window.confirm("This will open a new tab, is that okay?")) {
      window.open("https://github.com/padraigfl");
    }
  }
}];

var startMenuData = [{
  title: "Programs",
  icon: folderProgram24Min,
  options: programs
}, {
  title: "Favorites",
  icon: folderFavorites24Min,
  options: favorites
}, {
  title: "Documents",
  icon: folderOpen24Min,
  options: []
}];

var facepalm = "THIS IS BROKEN IN FIREFOX, FIX SUGGESTIONS APPRECIATED\n" + "............................................________ \n" + "....................................,.-'\"...................``~., \n" + '.............................,.-"..................................."-., \n' + '.........................,/...............................................":, \n' + ".....................,?......................................................, \n" + ".................../...........................................................,} \n" + "................./......................................................,:`^`..} \n" + '.............../...................................................,:"........./ \n' + "..............?.....__.........................................:`.........../ \n" + '............./__.(....."~-,_..............................,:`........../ \n' + '.........../(_...."~,_........"~,_....................,:`........_/ \n' + '..........{.._$;_......"=,_......."-,_.......,.-~-,},.~";/....} \n' + '...........((.....*~_......."=-._......";,,./`..../"............../ \n' + '...,,,___.`~,......"~.,....................`.....}............../ \n' + '............(....`=-,,.......`........................(......;_,,-" \n' + "............/.`~,......`-...................................../ \n" + ".............`~.*-,.....................................|,./.....,__ \n" + ",,_..........}.>-._...................................|..............`=~-, \n" + ".....`=~-,__......`,................................. \n" + "...................`=~-,,.,............................... \n" + "................................`:,,...........................`..............__ \n" + ".....................................`=-,...................,%`>--==`` \n" + "........................................_..........._,-%.......` \n" + "..................................., ;\n";

var resume = "\n    ____            __           _          ________                __\n   / __ \\____ _____/ /________ _(_)___ _   / ____/ /___  ____  ____/ /\n  / /_/ / __ `/ __  / ___/ __ `/ / __ `/  / /_  / / __ \\/ __ \\/ __  / \n / ____/ /_/ / /_/ / /  / /_/ / / /_/ /  / __/ / / /_/ / /_/ / /_/ /  \n/_/    \\__,_/\\__,_/_/   \\__,_/_/\\__, /  /_/   /_/\\____/\\____/\\__,_/   \n                               /____/       \n================================================================\nFrontend Developer | London | padraig.flood1@gmail.com\n================================================================\nLikes to work with React and JavaScript\nLikes to have dumb side projects (the liberation of writing almost no tests!)\nLikes to write efficient code and make fun things\nLooking for projects to collab on and other fun stuff to do \n\nGithub: https://www.github.com/padraigfl\nLinkedIn: whatever, that site's a privacy nightmare, I'm sure you can find me\nPhone: HAHAHAHA I'm not putting that up here\n";

var desktopData = [{
  title: "My Computer",
  icon: computer32Min,
  Component: Explorer,
  data: {
    content: "Lets not go crazy here, don't write an OS in JS..."
  }
}, {
  title: "Component Library that I made for this thing",
  icon: htmlFile32Min,
  type: "ExternalLink",
  onClick: function onClick() {
    if (window.confirm("This will open a new tab, is that okay?")) {
      window.open("https://github.com/padraigfl/packard-belle");
    }
  }
}, {
  title: "Paint",
  icon: paint32Min,
  Component: IFrame,
  data: { src: "https://jspaint.app/" }
}, {
  title: "resume draft 31 final last",
  icon: notepadFile32Min,
  Component: Notepad,
  data: {
    content: resume
  }
}, {
  title: "facepalm",
  icon: notepadFile32Min,
  Component: Notepad,
  data: {
    content: facepalm
  }
}];

var ProgramContext = React.createContext();

var settings = function settings() {
  var injectedData = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : [];
  return [[].concat(toConsumableArray(injectedData), [{
    title: "Printers",
    icon: settingsPrinters16Min,
    Component: Explorer,
    isDisabled: true
  }, {
    title: "Folder Options",
    icon: folderOptions16Min,
    isDisabled: true
  }, {
    title: "Active Desktop",
    icon: activeDesktop16Min,
    isDisabled: true
  }]), {
    title: "Windows Update...",
    icon: windowsUpdate16Min
  }];
};

var startMenu = function startMenu() {
  var injectedData = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : [];
  var set$$1 = arguments[1];
  var shutDown = arguments[2];
  return [{
    title: "Windows Update",
    icon: windowsUpdate24Min,
    isDisabled: true
  }, [].concat(toConsumableArray(injectedData), [{
    title: "Settings",
    icon: settings24Min,
    options: settings(set$$1)
  }, {
    title: "Help",
    icon: help24Min,
    options: [{
      title: "Suport Me?",
      icon: htmlFile16Min,
      onClick: function onClick() {
        return window.open("https://www.buymeacoffee.com/padraig");
      }
    }]
  }, {
    title: "Run...",
    icon: run24Min,
    options: []
  }]), {
    title: "Log Off",
    icon: logOff24Min,
    isDisabled: true
  }, {
    title: "Shut Down...",
    icon: shutDown24,
    onClick: shutDown
  }];
};

var sameProgram = function sameProgram(a) {
  return function (b) {
    return a === b.id;
  };
};
var notSameProgram = function notSameProgram(a) {
  return function (b) {
    return a !== b.id;
  };
};

var addIdsToData = function addIdsToData(data) {
  return Array.isArray(data) ? data.map(function (d) {
    if (Array.isArray(d)) {
      return addIdsToData(d);
    }
    return _extends$2({}, d, {
      id: nanoid(),
      options: addIdsToData(d.options)
    });
  }) : undefined;
};

var desktopWithIds = function desktopWithIds(desktopData$$1) {
  return addIdsToData(desktopData$$1).map(function (entry) {
    var onClick = entry.onClick,
        data = objectWithoutProperties$1(entry, ["onClick"]);

    return _extends$2({}, data, {
      onDoubleClick: onClick
    });
  });
};

var initialize = function initialize(open, data, doubleClick) {
  return Array.isArray(data) ? data.map(function (d) {
    if (Array.isArray(d)) {
      return initialize(open, d);
    }
    var onClick = d.onClick,
        nestedData = objectWithoutProperties$1(d, ["onClick"]);

    var onClickAction = !d.options ? function () {
      if (d.Component) {
        open(d);
      }
      if (d.onClick) {
        d.onClick.apply(d, arguments);
      }
      if (d.onDoubleClick) {
        d.onDoubleClick.apply(d, arguments);
      }
    } : undefined;
    return _extends$2({}, nestedData, {
      onClick: !doubleClick ? onClickAction : undefined,
      onDoubleClick: doubleClick ? onClick : undefined,
      options: initialize(open, d.options)
    });
  }) : undefined;
};

var ProgramProvider = function (_Component) {
  inherits$1(ProgramProvider, _Component);

  function ProgramProvider() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, ProgramProvider);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = ProgramProvider.__proto__ || Object.getPrototypeOf(ProgramProvider)).call.apply(_ref, [this].concat(args))), _this), _this.state = {
      startMenu: initialize(function (p) {
        return _this.open(p);
      }, addIdsToData(startMenu(_this.props.startMenuData, [{ title: "Ctrl+Alt+Del", onClick: function onClick() {
          return _this.toggleTaskManager();
        } }, {
        title: "Control Panel",
        onClick: function onClick() {
          return _this.toggleSettings();
        },
        icon: controlPanel16Min
      }], function () {
        return _this.toggleShutDownMenu();
      }))),
      desktop: [].concat(toConsumableArray(initialize(function (p) {
        return _this.open(p);
      }, desktopWithIds(_this.props.desktopData)).map(function (entry) {
        var onClick = entry.onClick,
            data = objectWithoutProperties$1(entry, ["onClick"]);

        return _extends$2({}, data, {
          onDoubleClick: onClick
        });
      })), [{
        title: "Control Panel",
        icon: controlPanel16Min,
        onDoubleClick: function onDoubleClick() {
          return _this.toggleSettings(true);
        }
      }]),
      quickLaunch: [{
        onClick: function onClick() {
          return _this.minimizeAll();
        },
        icon: activeDesktop16Min,
        title: "Display Desktop"
      }],
      activePrograms: [],
      openOrder: [],
      settingsDisplay: false,
      shutDownMenu: false
    }, _this.toggleShutDownMenu = function () {
      return _this.setState(function (state) {
        return { shutDownMenu: !state.shutDownMenu };
      });
    }, _this.toggleTaskManager = function () {
      return _this.setState(function (state) {
        return { taskManager: !state.taskManager };
      });
    }, _this.toggleSettings = function (val) {
      return _this.setState(function (state) {
        return {
          settingsDisplay: val || !state.settingsDisplay
        };
      });
    }, _this.shutDown = function () {
      var desktop = document.querySelector(".desktop");
      if (desktop) {
        desktop.innerHTML = "";
        desktop.classList.add("windowsShuttingDown");
        setTimeout(function () {
          desktop.classList.replace("windowsShuttingDown", "itIsNowSafeToTurnOffYourComputer");
          window.localStorage.removeItem("loggedIn");
        }, 3000);
      }
    }, _this.isProgramActive = function (programId) {
      return _this.state.activePrograms.some(sameProgram(programId));
    }, _this.exit = function (programId) {
      return _this.setState({
        activePrograms: _this.state.activePrograms.filter(notSameProgram(programId)),
        openOrder: _this.state.openOrder.filter(function (x) {
          return x !== programId;
        }),
        activeId: null
      });
    }, _this.moveToTop = function (programId) {
      var programIndex = _this.state.activePrograms.findIndex(sameProgram(programId));
      if (programIndex === -1) {
        return;
      }
      _this.setState({
        activePrograms: [].concat(toConsumableArray(_this.state.activePrograms.filter(notSameProgram(programId))), [_extends$2({}, _this.state.activePrograms[programIndex], {
          minimized: false
        })]),
        activeId: programId
      });
    }, _this.open = function (program) {
      if (!program.Component) {
        return;
      }
      if (_this.isProgramActive(program) && !program.multiWindow) {
        _this.moveToTop(program);
        return;
      }
      var newProgram = _extends$2({}, program, {
        id: program.multiWindow ? nanoid() : program.id
      });
      _this.setState({
        activePrograms: [].concat(toConsumableArray(_this.state.activePrograms), [newProgram]),
        openOrder: [].concat(toConsumableArray(_this.state.openOrder), [newProgram.id]),
        activeId: newProgram.id
      });
    }, _this.close = function (program, exit) {
      if (!_this.isProgramActive(program)) {
        return;
      }

      var taskBar = _this.state.openOrder.filter(function (p) {
        return p !== program.id;
      });
      _this.setState({ openOrder: taskBar });

      if (!program.background || exit) {
        _this.exit(program);
      }
    }, _this.minimize = function (programId) {
      if (!_this.isProgramActive(programId)) {
        return;
      } else {
        var programIndex = _this.state.activePrograms.findIndex(sameProgram(programId));
        _this.setState({
          activePrograms: [_extends$2({}, _this.state.activePrograms[programIndex], {
            minimized: true
          })].concat(toConsumableArray(_this.state.activePrograms.filter(function (prog) {
            return prog.id !== programId;
          }))),
          activeId: null
        });
      }
    }, _this.minimizeAll = function () {
      return _this.setState(function (state) {
        return {
          activePrograms: state.activePrograms.map(function (p) {
            return _extends$2({}, p, {
              minimized: true
            });
          }),
          activeId: null
        };
      });
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(ProgramProvider, [{
    key: "render",
    value: function render() {
      return React__default.createElement(
        ProgramContext.Provider,
        {
          value: _extends$2({}, this.state, {
            onOpen: this.open,
            onClose: this.close,
            moveToTop: this.moveToTop,
            toggleTaskManager: this.toggleTaskManager,
            toggleSettings: this.toggleSettings,
            toggleShutDownMenu: this.toggleShutDownMenu,
            shutDown: this.shutDown,
            onMinimize: this.minimize
          })
        },
        this.props.children
      );
    }
  }]);
  return ProgramProvider;
}(React.Component);

ProgramProvider.defaultProps = {
  startMenuData: startMenuData,
  desktopData: desktopData
};

var TaskBar$1 = function TaskBar$$1() {
  return React__default.createElement(
    ProgramContext.Consumer,
    null,
    function (context) {
      return React__default.createElement(TaskBar, {
        options: context.startMenu,
        quickLaunch: context.quickLaunch,
        openWindows: context.openOrder.map(function (p) {
          var activePrograms = context.activePrograms;

          var programIdx = activePrograms.findIndex(function (x) {
            return x.id === p;
          });
          var isActive = p === context.activeId;
          var _onClick = isActive ? context.onMinimize : context.moveToTop;
          var _activePrograms$progr = activePrograms[programIdx],
              title = _activePrograms$progr.title,
              icon = _activePrograms$progr.icon;

          return {
            title: title,
            icon: icon,
            isActive: isActive,
            onClick: function onClick() {
              return _onClick(p);
            }
          };
        })
      });
    }
  );
};

var WindowManager = function (_Component) {
  inherits$1(WindowManager, _Component);

  function WindowManager() {
    classCallCheck$1(this, WindowManager);
    return possibleConstructorReturn$1(this, (WindowManager.__proto__ || Object.getPrototypeOf(WindowManager)).apply(this, arguments));
  }

  createClass$1(WindowManager, [{
    key: "render",
    value: function render() {
      var _this2 = this;

      return React__default.createElement(
        React__default.Fragment,
        null,
        this.context.activePrograms.filter(function (prog) {
          return !prog.minimized;
        }).map(function (prog) {
          return React__default.createElement(prog.Component, _extends$2({}, prog, {
            key: prog.id || prog.key,
            onClose: _this2.context.onClose,
            onMinimize: _this2.context.onMinimize,
            moveToTop: _this2.context.moveToTop,
            isActive: prog.id === _this2.context.activeId
          }));
        })
      );
    }
  }]);
  return WindowManager;
}(React.Component);

WindowManager.contextType = ProgramContext;

var css$x = "._task-manager_TaskManager__Z5r0a {\n  padding: 3px; }\n  ._task-manager_TaskManager__Z5r0a ._task-manager_SelectBox__1SHU1 {\n    height: 100px;\n    width: initial;\n    margin: 4px; }\n  ._task-manager_TaskManager__buttons__1cEQn {\n    display: flex;\n    align-items: center;\n    padding-right: 4px;\n    padding-left: 4px; }\n    ._task-manager_TaskManager__buttons__1cEQn ._task-manager_btn__1ttsc:first-child {\n      margin-left: auto; }\n    ._task-manager_TaskManager__buttons__1cEQn ._task-manager_btn__1ttsc {\n      margin-left: 4px;\n      margin-bottom: 8px;\n      width: 60px; }\n";
var styles$4 = { "TaskManager": "_task-manager_TaskManager__Z5r0a", "SelectBox": "_task-manager_SelectBox__1SHU1", "TaskManager__buttons": "_task-manager_TaskManager__buttons__1cEQn", "btn": "_task-manager_btn__1ttsc" };
styleInject$1(css$x);

var TaskManager = function (_Component) {
  inherits$1(TaskManager, _Component);

  function TaskManager() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, TaskManager);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = TaskManager.__proto__ || Object.getPrototypeOf(TaskManager)).call.apply(_ref, [this].concat(args))), _this), _this.state = {
      selected: null
    }, _this.onSelect = function (selected) {
      return _this.setState({ selected: selected });
    }, _this.exit = function () {
      if (_this.state.selected) {
        _this.context.onClose(_this.state.selected, true);
      }
    }, _this.moveToTop = function () {
      if (_this.state.selected) {
        _this.context.moveToTop(_this.state.selected);
      }
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(TaskManager, [{
    key: "render",
    value: function render() {
      var context = this.context,
          props = this.props;

      return context.taskManager ? React__default.createElement(
        Window,
        _extends$2({}, props, {
          resizable: false,
          initialX: 200,
          initialY: 150,
          initialWidth: 240,
          initialHeight: 240,
          Component: WindowProgram,
          title: "Task Manager",
          className: styles$4.TaskManager,
          onHelp: function onHelp() {} // @todo
          , onClose: context.toggleTaskManager,
          menuOptions: buildMenu(_extends$2({}, props, {
            onClose: context.toggleTaskManager
          }))
        }),
        React__default.createElement(SelectBox, {
          className: styles$4.SelectBox,
          onClick: this.onSelect,
          options: context.openOrder.map(function (pid) {
            var prog = context.activePrograms.find(function (p) {
              return p.id === pid;
            });
            return {
              title: prog.title,
              value: prog.id // key is based on value
            };
          }),
          selected: [this.state.selected]
        }),
        React__default.createElement(
          "div",
          { className: styles$4.TaskManager__buttons },
          React__default.createElement(
            ButtonForm,
            { onClick: this.exit },
            "End Task"
          ),
          React__default.createElement(
            ButtonForm,
            { onClick: this.moveToTop },
            "Switch To"
          ),
          React__default.createElement(
            ButtonForm,
            { isDisabled: true },
            "New Task"
          )
        )
      ) : null;
    }
  }]);
  return TaskManager;
}(React.Component);

TaskManager.contextType = ProgramContext;

var css$y = "._styles_DesktopView__1aO5R {\n  padding-bottom: 32px; }\n";
var styles$5 = { "DesktopView": "_styles_DesktopView__1aO5R" };
styleInject$1(css$y);

var DesktopView = function DesktopView() {
  return React__default.createElement(
    ProgramContext.Consumer,
    null,
    function (context) {
      return React__default.createElement(
        ExplorerView,
        { className: styles$5.DesktopView },
        context.desktop.map(function (option) {
          return React__default.createElement(ExplorerIcon, _extends$2({ key: option.title }, option));
        })
      );
    }
  );
};

var css$z = "._styles_Settings__10c3j ._styles_DetailsSection__21co4 {\n  display: flex;\n  flex-direction: column; }\n\n._styles_Settings__10c3j ._styles_Checkbox__3GNmn {\n  margin: 4px; }\n\n._styles_Settings__10c3j ._styles_Radio__3pn7G {\n  margin: auto 2px; }\n";
var styles$6 = { "Settings": "_styles_Settings__10c3j", "DetailsSection": "_styles_DetailsSection__21co4", "Checkbox": "_styles_Checkbox__3GNmn", "Radio": "_styles_Radio__3pn7G" };
styleInject$1(css$z);

var Settings = function (_Component) {
  inherits$1(Settings, _Component);

  function Settings() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, Settings);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = Settings.__proto__ || Object.getPrototypeOf(Settings)).call.apply(_ref, [this].concat(args))), _this), _this.state = {
      selected: null,
      bgImg: _this.context.bgImg,
      bgStyle: _this.context.bgStyle
    }, _this.onSelect = function (selected) {
      return _this.setState({ selected: selected });
    }, _this.exit = function () {
      if (_this.state.selected) {
        _this.context.onClose(_this.state.selected, true);
      }
    }, _this.moveToTop = function () {
      if (_this.state.selected) {
        _this.context.moveToTop(_this.state.selected);
      }
    }, _this.tempChange = function (func, revertFunc) {
      func();
      setTimeout(function () {
        if (window.confirm("Please confirm this change looks okay")) {
          return;
        }
        revertFunc();
      }, 500);
    }, _this.updateBackground = function () {
      _this.context.updateLocalStorage("bgImg", _this.state.bgImg);
    }, _this.updateBackgroundStyle = function (e) {
      var val = e.target.value;
      _this.context.updateLocalStorage("bgStyle", val);
    }, _this.removeBackground = function () {
      _this.context.removeLocalStorage(["bgImg", "bgStyle"]);
      _this.setState({ bgImg: null, bgStyle: null });
    }, _this.handleFileRead = function () {
      var content = _this.fileReader.result;
      if (content.length < 120000) {
        _this.setState({ bgImg: content });
      } else {
        window.alert("100kb or less please, sorry =/");
      }
    }, _this.handleFileChosen = function (_ref2) {
      var files = _ref2.target.files;

      _this.fileReader = new FileReader();
      _this.fileReader.onloadend = _this.handleFileRead;
      _this.fileReader.readAsDataURL(files[0]);
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(Settings, [{
    key: "render",
    value: function render() {
      var _this2 = this;

      var context = this.context,
          props = this.props;

      return React__default.createElement(
        ProgramContext.Consumer,
        null,
        function (program) {
          return program.settingsDisplay && React__default.createElement(
            Window,
            _extends$2({}, props, {
              initialX: 200,
              initialY: 100,
              initialWidth: 280,
              initialHeight: 320,
              Component: WindowAbstract,
              title: "Control Panel",
              className: "Settings",
              onHelp: function onHelp() {} // @todo
              , onClose: function onClose() {
                return program.toggleSettings(false);
              },
              menuOptions: buildMenu(_extends$2({}, props, {
                onClose: program.toggleSettings
              })),
              resizable: false,
              onMinimize: null,
              onMaximize: null
            }),
            React__default.createElement(
              DetailsSection,
              { className: styles$6.DetailsSection },
              "Best avoid all these other than CRT on mobile"
            ),
            React__default.createElement(
              DetailsSection,
              { title: "Customise" },
              React__default.createElement(Checkbox, {
                id: "Mobile Portrait View",
                label: "Mobile Portrait View",
                onChange: context.toggleMobile,
                checked: context.isMobile === true,
                className: styles$6.Checkbox
              }),
              React__default.createElement(Checkbox, {
                id: "CRT Effect",
                label: "CRT Effect",
                onChange: context.toggleCrt,
                checked: context.crt === true,
                className: styles$6.Checkbox
              }),
              React__default.createElement(Checkbox, {
                id: "Fullscreen",
                label: "Fullscreen",
                onChange: context.toggleFullScreen,
                checked: context.fullScreen === true,
                className: styles$6.Checkbox
              })
            ),
            !context.isMobile && React__default.createElement(
              DetailsSection,
              { title: "Scale Options (Confirmation Prompt)" },
              React__default.createElement(
                "div",
                { className: "options-row" },
                [1, 1.5, 2].map(function (scale) {
                  return React__default.createElement(Radio, {
                    id: scale,
                    label: scale * 100 + "%",
                    value: scale,
                    onChange: function onChange(e) {
                      _this2.tempChange(function () {
                        return context.changeScale(+e.target.value);
                      }, function () {
                        return context.changeScale(context.scale);
                      });
                    },
                    checked: context.scale === scale,
                    isDisabled: context.fullScreen,
                    className: styles$6.Radio
                  });
                })
              )
            ),
            React__default.createElement(
              DetailsSection,
              { title: "Background" },
              _this2.context.bgImg ? React__default.createElement(
                React__default.Fragment,
                null,
                React__default.createElement(
                  "div",
                  null,
                  ["tile", "stretch", "contain"].map(function (v) {
                    return React__default.createElement(Radio, {
                      key: v,
                      id: v,
                      label: v,
                      value: v,
                      onChange: _this2.updateBackgroundStyle,
                      checked: _this2.context.bgStyle === v,
                      className: styles$6.Radio
                    });
                  })
                ),
                React__default.createElement(
                  ButtonForm,
                  { onClick: _this2.removeBackground },
                  "Reset Background"
                )
              ) : React__default.createElement(
                "div",
                null,
                React__default.createElement("input", {
                  type: "file",
                  onChange: _this2.handleFileChosen,
                  name: "bgImg",
                  id: "bgImg"
                }),
                React__default.createElement(
                  "div",
                  null,
                  React__default.createElement(
                    ButtonForm,
                    {
                      onClick: _this2.updateBackground,
                      isDisabled: !_this2.state.bgImg
                    },
                    "Upload Image"
                  )
                )
              )
            ),
            _this2.state.tempChange && "Previewing Changes"
          );
        }
      );
    }
  }]);
  return Settings;
}(React.Component);

Settings.contextType = SettingsContext;

var css$A = "@keyframes _crt_flicker__2CgQm {\n  0% {\n    opacity: 0.05503; }\n  5% {\n    opacity: 0.80451; }\n  10% {\n    opacity: 0.75658; }\n  15% {\n    opacity: 0.51557; }\n  20% {\n    opacity: 0.44762; }\n  25% {\n    opacity: 0.94009; }\n  30% {\n    opacity: 0.58387; }\n  35% {\n    opacity: 0.29045; }\n  40% {\n    opacity: 0.92332; }\n  45% {\n    opacity: 0.6094; }\n  50% {\n    opacity: 0.95549; }\n  55% {\n    opacity: 0.69498; }\n  60% {\n    opacity: 0.76091; }\n  65% {\n    opacity: 0.81461; }\n  70% {\n    opacity: 0.73123; }\n  75% {\n    opacity: 0.5302; }\n  80% {\n    opacity: 0.65145; }\n  85% {\n    opacity: 0.95242; }\n  90% {\n    opacity: 0.33396; }\n  95% {\n    opacity: 0.14238; }\n  100% {\n    opacity: 0.62107; } }\n\n._crt_container__3JLx- {\n  width: 100%;\n  height: 100%;\n  top: 0px;\n  left: 0px;\n  position: absolute;\n  overflow: hidden;\n  z-index: 100;\n  pointer-events: none; }\n  ._crt_container__3JLx-::after {\n    content: \" \";\n    display: block;\n    position: absolute;\n    top: 0;\n    left: 0;\n    bottom: 0;\n    right: 0;\n    background: rgba(18, 16, 16, 0.02);\n    opacity: 0;\n    z-index: 2;\n    pointer-events: none; }\n  ._crt_container__3JLx-::before {\n    content: \" \";\n    display: block;\n    position: absolute;\n    top: 0;\n    left: 0;\n    bottom: 0;\n    right: 0;\n    background: linear-gradient(rgba(18, 16, 16, 0) 50%, rgba(0, 0, 0, 0.25) 50%), linear-gradient(90deg, rgba(255, 0, 0, 0.06), rgba(0, 255, 0, 0.02), rgba(0, 0, 255, 0.06));\n    z-index: 2;\n    background-size: 100% 2px, 3px 100%;\n    pointer-events: none; }\n\n._crt_container__3JLx-::after {\n  animation: _crt_flicker__2CgQm 0.15s infinite; }\n\n@keyframes _crt_turn-on__gElsq {\n  0% {\n    transform: scale(1, 0.8) translate3d(0, 0, 0);\n    -webkit-filter: brightness(30);\n    filter: brightness(30);\n    opacity: 1; }\n  3.5% {\n    transform: scale(1, 0.8) translate3d(0, 100%, 0); }\n  3.6% {\n    transform: scale(1, 0.8) translate3d(0, -100%, 0);\n    opacity: 1; }\n  9% {\n    transform: scale(1.3, 0.6) translate3d(0, 100%, 0);\n    -webkit-filter: brightness(30);\n    filter: brightness(30);\n    opacity: 0; }\n  11% {\n    transform: scale(1, 1) translate3d(0, 0, 0);\n    -webkit-filter: contrast(0) brightness(0);\n    filter: contrast(0) brightness(0);\n    opacity: 0; }\n  100% {\n    transform: scale(1, 1) translate3d(0, 0, 0);\n    -webkit-filter: contrast(1) brightness(1.2) saturate(1.3);\n    filter: contrast(1) brightness(1.2) saturate(1.3);\n    opacity: 1; } }\n\n@keyframes _crt_turn-off__2cV4W {\n  0% {\n    transform: scale(1, 1.3) translate3d(0, 0, 0);\n    -webkit-filter: brightness(1);\n    filter: brightness(1);\n    opacity: 1; }\n  60% {\n    transform: scale(1.3, 0.001) translate3d(0, 0, 0);\n    -webkit-filter: brightness(10);\n    filter: brightness(10); }\n  100% {\n    animation-timing-function: cubic-bezier(0.755, 0.05, 0.855, 0.06);\n    transform: scale(0, 0.0001) translate3d(0, 0, 0);\n    -webkit-filter: brightness(50);\n    filter: brightness(50); } }\n\n._crt_screen__2s-ux {\n  width: 100%;\n  height: 100%;\n  border: none; }\n\n._crt_container__3JLx- > ._crt_screen__2s-ux {\n  animation: _crt_turn-off__2cV4W 0.55s cubic-bezier(0.23, 1, 0.32, 1);\n  animation-fill-mode: forwards; }\n\n._crt_container__3JLx- > ._crt_screen__2s-ux {\n  animation: _crt_turn-on__gElsq 4s linear;\n  animation-fill-mode: forwards; }\n\n@keyframes _crt_overlay-anim__26jqV {\n  0% {\n    visibility: hidden; }\n  20% {\n    visibility: hidden; }\n  21% {\n    visibility: visible; }\n  100% {\n    visibility: hidden; } }\n\n._crt_overlay__2Eanq {\n  color: #00ff00;\n  position: absolute;\n  top: 20px;\n  left: 20px;\n  font-size: 60px;\n  visibility: hidden;\n  pointer-events: none; }\n\n._crt_container__3JLx- ._crt_overlay__2Eanq {\n  animation: _crt_overlay-anim__26jqV 5s linear;\n  animation-fill-mode: forwards; }\n";
var style = { "container": "_crt_container__3JLx-", "flicker": "_crt_flicker__2CgQm", "screen": "_crt_screen__2s-ux", "turn-off": "_crt_turn-off__2cV4W", "turn-on": "_crt_turn-on__gElsq", "overlay": "_crt_overlay__2Eanq", "overlay-anim": "_crt_overlay-anim__26jqV" };
styleInject$1(css$A);

var CRTOverlay = function CRTOverlay(props) {
  return React__default.createElement(
    "div",
    { className: style.container },
    React__default.createElement("div", { className: style.screen })
  );
};

var css$B = "._styles_ShutDown__1Svgh {\n  position: absolute;\n  top: 0px;\n  left: 0px;\n  width: 100%;\n  height: 100%;\n  display: flex;\n  flex-direction: column;\n  z-index: 15; }\n  ._styles_ShutDown__1Svgh:after {\n    transition: all linear 2s;\n    background-repeat: repeat;\n    background-image: url(\"data:image/gif;base64,R0lGODlhAgACAJEAAAAAAP///8zMzP///yH5BAEAAAMALAAAAAACAAIAAAID1CYFADs=\");\n    position: absolute;\n    width: 100%;\n    height: 1%;\n    content: \"\";\n    filter: brightness(0.2); }\n  ._styles_ShutDown__1Svgh._styles_animation__1wr6w:after {\n    height: 100%; }\n  ._styles_ShutDown__Window__2LmYO {\n    margin: auto;\n    z-index: 16; }\n  ._styles_ShutDown__Radio__3bW-v {\n    margin: 6px;\n    display: block; }\n  ._styles_ShutDown__content__2uDqH {\n    display: flex;\n    margin: 15px; }\n    ._styles_ShutDown__content__2uDqH img {\n      height: 32px;\n      margin-right: 12px; }\n    ._styles_ShutDown__content__2uDqH > div {\n      display: flex;\n      flex-direction: column; }\n  ._styles_ShutDown__buttons__1BOPj {\n    display: flex;\n    margin-top: 12px; }\n    ._styles_ShutDown__buttons__1BOPj ._styles_ButtonForm__1ms7Z {\n      margin-left: 4px;\n      flex-grow: 1; }\n";
var styles$7 = { "ShutDown": "_styles_ShutDown__1Svgh", "animation": "_styles_animation__1wr6w", "ShutDown__Window": "_styles_ShutDown__Window__2LmYO", "ShutDown__Radio": "_styles_ShutDown__Radio__3bW-v", "ShutDown__content": "_styles_ShutDown__content__2uDqH", "ShutDown__buttons": "_styles_ShutDown__buttons__1BOPj", "ButtonForm": "_styles_ButtonForm__1ms7Z" };
styleInject$1(css$B);

var OPTIONS = ["Shut Down", "Restart", "That third option I forget"];

var ShutDown = function (_Component) {
  inherits$1(ShutDown, _Component);

  function ShutDown() {
    var _ref;

    var _temp, _this, _ret;

    classCallCheck$1(this, ShutDown);

    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    return _ret = (_temp = (_this = possibleConstructorReturn$1(this, (_ref = ShutDown.__proto__ || Object.getPrototypeOf(ShutDown)).call.apply(_ref, [this].concat(args))), _this), _this.state = {
      selected: OPTIONS[0],
      display: _this.context.shutDownMenu
    }, _this.process = function () {
      if (_this.state.selected === OPTIONS[0]) {
        _this.context.shutDown();
        return;
      }
      if (_this.state.selected === OPTIONS[1]) {
        _this.context.restart();
        return;
      }
    }, _temp), possibleConstructorReturn$1(_this, _ret);
  }

  createClass$1(ShutDown, [{
    key: "componentDidUpdate",
    value: function componentDidUpdate() {
      var _this2 = this;

      if (this.context.shutDownMenu && this.context.shutDownMenu !== this.state.display) {
        setTimeout(function () {
          return _this2.setState({ display: _this2.context.shutDownMenu });
        });
        return;
      }
    }
  }, {
    key: "render",
    value: function render() {
      var _this3 = this;

      var context = this.context,
          props = this.props;

      return context.shutDownMenu ? React__default.createElement(
        "div",
        {
          className: cx(styles$7.ShutDown, props.className, defineProperty$1({}, styles$7.animation, this.state.display))
        },
        React__default.createElement(
          WindowAbstract,
          {
            className: styles$7.ShutDown__Window,
            title: "Shut Down Windows",
            onClose: context.toggleShutDownMenu,
            resizable: false
          },
          React__default.createElement(
            "div",
            { className: styles$7.ShutDown__content },
            React__default.createElement("img", { src: shutDown24, alt: "shut down" }),
            React__default.createElement(
              "div",
              null,
              "What do you want your computer to do?",
              OPTIONS.map(function (option) {
                return React__default.createElement(Radio, {
                  className: styles$7.ShutDown__Radio,
                  key: option,
                  value: option,
                  label: option,
                  onChange: function onChange() {
                    return _this3.setState({ selected: option });
                  },
                  checked: option === _this3.state.selected,
                  isDisabled: true
                });
              }),
              React__default.createElement(
                "div",
                { className: styles$7.ShutDown__buttons },
                React__default.createElement(
                  ButtonForm,
                  {
                    className: styles$7.ButtonForm,
                    onClick: this.process
                  },
                  "OK"
                ),
                React__default.createElement(
                  ButtonForm,
                  {
                    className: styles$7.ButtonForm,
                    onClick: context.toggleShutDownMenu
                  },
                  "Cancel"
                ),
                React__default.createElement(
                  ButtonForm,
                  { className: styles$7.ButtonForm, isDisabled: true },
                  "Help"
                )
              )
            )
          )
        )
      ) : null;
    }
  }]);
  return ShutDown;
}(React.Component);

ShutDown.contextType = ProgramContext;

var css$C = "._background_Background__3zwK7 {\n  position: absolute;\n  left: 0px;\n  top: 0px;\n  height: 100%;\n  width: 100%;\n  pointer-events: none; }\n  ._background_Background__3zwK7 div {\n    height: 100%;\n    width: 100%; }\n  ._background_Background--tiled__3J2OS div {\n    background-size: 40px;\n    background-repeat: repeat; }\n  ._background_Background--contain__oc4Fj div {\n    background-size: 80%;\n    background-position: center;\n    background-repeat: no-repeat; }\n  ._background_Background--stretch__2eNGe div {\n    background-size: 100% 100%;\n    background-repeat: no-repeat; }\n";
var styles$8 = { "Background": "_background_Background__3zwK7", "Background--tiled": "_background_Background--tiled__3J2OS", "Background--contain": "_background_Background--contain__oc4Fj", "Background--stretch": "_background_Background--stretch__2eNGe" };
styleInject$1(css$C);

var Background = function Background(props) {
  return React__default.createElement(
    SettingsContext.Consumer,
    null,
    function (context) {
      var _cx;

      return context.bgImg ? React__default.createElement(
        "div",
        {
          className: cx(styles$8.Background, (_cx = {}, defineProperty$1(_cx, styles$8["Background--tiled"], context.bgStyle === "tile"), defineProperty$1(_cx, styles$8["Background--contain"], context.bgStyle === "contain"), defineProperty$1(_cx, styles$8["Background--stretch"], context.bgStyle === "stretch"), _cx))
        },
        React__default.createElement("div", { style: { backgroundImage: "url(" + context.bgImg + ")" } })
      ) : null;
    }
  );
};

var css$D = "@font-face {\n  font-family: AMIBios;\n  src: url(./assets/ami_bios1.woff2) format(\"woff2\"); }\n\n.App_desktop__qsEUr.App_screen__27vyv {\n  position: relative;\n  display: flex;\n  flex-grow: 1;\n  flex-direction: column;\n  align-content: center;\n  align-items: center; }\n\n.App_desktop__qsEUr.App_desktopX2__1ZELF {\n  transform: scale(2); }\n\n.App_desktop__qsEUr.App_desktopX1_5__y1HFf {\n  transform: scale(1.5); }\n\n.App_StandardMenuItem__button__2GEmZ {\n  padding-top: 1px; }\n\n.App_Window__3kPTJ.App_Window--maximized__37H1C {\n  width: calc(100% + 4px);\n  height: calc(100% + 4px); }\n\n.itIsNowSafeToTurnOffYourComputer {\n  background-color: #000000 !important;\n  display: flex; }\n\n.itIsNowSafeToTurnOffYourComputer:after {\n  content: \"It's now safe to turn off your computer.\";\n  padding: 16px;\n  text-align: center;\n  color: orange;\n  margin: auto;\n  font-size: 22px;\n  font-family: AMIBios, MSSansSerif, \"Courier New\", Courier, monospace; }\n\n.desktop.windowsShuttingDown {\n  background-color: #a6c7df;\n  background-image: url(\"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAoAAAAGQCAMAAAAJLSEXAAAByFBMVEW2z+fH1+ff5+/n7/e+1+eux9/P3++uz+emx98AAADH1+++z+fX5+/X3++evt/v7/e+1+/n5++ux+fH3+/n7+/v7+/f5/cICAi21+euz9+mx+cQEBCmvt/f7/fv9/cYGBi2z99Rhr4YUZ4oKCggICBhjsfX5/fXaRD/7wCex9/naQg4ODjP3+dBQUEwMDD/3wBZWVj39/ffWQEQOI7X4OdJSUmWrs9hYWnfSQCmz3nn5/fQ1+fo6OdRUVGGho6urq6evtdNdbb/zwCOlpaOwFZpaWmOnr6ex3F5vUjPz8++vr7v9/+hpqZxcXHf3+emz+e2x99BSVG21+95eXnf6OeGnscwYaZJaa7f3+/P1++Wx2mex3k4OEFpjse+z9/N19+enp7H3+fP5+/4+P/kbRRBQUkZFw+utteGh4T/xwDvz7YnMUPXRgDv5+/f7+/flmnrsopGZonZYynHSABCQTfsjjjvqEOex+fv9+9dbDretqauUQ3nhiAwKyj339fjuwiSeSXyq11+kF/fppY4QVGWtHRbLw6+3+/DqR3318dpUBG2lgPn1wuu0uyertdRhiimnkmLRggwSSBhnjA0IgQlR3FBMCiu13muA9znAADBI0lEQVR42sydy06bSRSEbQJhZEByIEKAFIkV0kgssyIPMSiryTJ5gHn/5eSkqFSd0/3fbBKnJWcI8eV3/1/XuXbP6q/v4/Ly5Me4vDx9GauXcXNzfLzdbjbxyOP4eLU6/jE2m6urL1/eNuPi+zg/v7iIn6+u/JXx2tcdxy9jvb66is87/zHw2fh0fGZ8t5OX8ddvGX//XX8Tn3xycnp6f1+vvo6zs3jEM+Kn+HYxfHaPXsb19ZvBEf/Gf//w4c2bp6f4+/V1vC7P02azXsdM4TP1udstGODQHTztjKBp/vysNC0YcYME4c0NEBwDEJOy2fQQDBTw9QLTXwtgTEy8vwA8PyeA6zU/lVP0uwDsDc40EQRqFT6MjIIQDPwI4PV1gEXA4s+ALH6+fhlAEPh9+CD84qFlCvwcQM4rEYxH/O3mRnMfpOCBcXt7ebkDgHd3UkEg6BqIW+sjfheTEhed16UjGAgAg8APz81rbP+hmxfvHgoYN+fhQWsb6APA+3tM0aEBBH7xCMx6ypdnCXOdZ7rqHzEUfoANQPJZwI8I6o5RHCr0ca/jruGuQwEdQB9EcP7srtqJkQoSQJjhqoAyewCLq5K6w4n69k0YAMPXBRBXgSukAQ784sHJdewDv8MiiKVO/KB24/i5AkLjY64BUTW/1DuCdn0dqkcE8Rq8zg1w6B/ujH+u5hUPGmBoIB8thPMtzKq3Nt0I4yJaAHkp65cR0wIAHx6kgvACgWR8Bayk1zPCdATi+kL94iqEn64E2PNVQPCwAN7eEqysf/hbNr96Xszfp0+YWZhQAegKB/UDfjS8eAjAqn9wU7L+xbzCfhA/KWAfPyA438lZ9dbmP/9kPxBC3AIIBN00YFVKeYiga+B6Ha97XfwAtgKQuAascHwuwhBO7mGNMF0deICuf/iJf/ZcjZhnfksg5PrnXh/QPDoCdMCPv2/xwx1s9U/al+/4MHyc4R0VsKpgXwO32xwRMRBBXIYbXxFUPPpaRth9v83m61cBSP+mKqA+9ZAKCABvb5+f4zswBCF6/G//+1IBMdOOH37KiEEBM5TCL5vf6v9hacecuvnlHf/8ORb/MILzjXAXwFAHIAgFhBjXYNzxi0ulXxIDX45RsNYaV9O+Cnh2Bl0mfjGBwK+ngAyBshE+DIBIwsSn07C6/nnsC4VkqAIkqIDAB3jJ76uQwTwzFGkBHDa/Q/onBfz8efjuxOKeB+D3Wej/Ggi6Ed5uK3p8EEIaBri+TITQC3QNVFJkH90jfjDAwu/hgfi5N1o/dYmj/GsUUJ6dwMvqd38fMbsQPDsLAEMBCaDwCxN7dFTx65le4TemfwQQCpgB3G6n7tK82f0hce2v4UDWfGBGkJGnzAfzb3B7gSFSIcIwh/v7okftwypV4ofZMXw6f69k9J8BYA4uHEThxwKBFFCWBtYm/D7GuYxsswFWyiUD6P5fD7+sgBm/Me+PczvHCxwAkDlBj4SZjPELicuIW8oEgRthIliV0EOCfdCj6vHh+EEB6QMSQWYgDw9gWwdxFRR+z89KGHkihm4Nvb4INBD6ASyvjxx1h5vfYfy22773N4Xf3ETMS5QxtEbHjDC8KV0IE5bUQKY/ufqEIEFxf2wZfkpnM+wQfvA5Q/tohGWCAb0r7yEVUPhVz08AnvwcMNfE7+ICZThm9aByTLx7hWQaP3l/+dPjfjP54vGve34qvvXxG5/dn3SNJQpubz0SzgqY14FrYHxJRxBalCPjJdWQjB/rHSi6CT7G2wEf1cANjTydwyogbEteYPyzZ36VsEEUTKV388pFTjRVIxnCb0r/4FRl/JR8bqvAFT8Y4OH5JX4DAGqiAkEvyXkAokqgpocRWsCHoaJ3DkXW6+X6B/Q85KitD/jstswOw48MJCf7cPrHJHSFsOLH5yMIEX50dKB1yjnEt81NCi1+nqVV8a0CeHPDCojjJ/07HRnAb2x5C79RAMeMsCuJcvpykWmImZlyP5AJmWkj3MKHuKzCF+8aBT/eEEy0l+LiNTn4QargEABeXirJ0huOHwFkUCD9o7/nKS/ViPsIEj/egSH9kwfIildtP3DcFLTCY4XXOobfDABzZ0w1wlJANuDQS2GePiYBMRqTABXBq6spACt+9Emq0aXyefjB2/LtG/FTL86hFRBWpXpOU/hFCkbfmfjV0icDsZ4KVlTH8avNBwCwRU+uQh5DBtib/kYV0CsiPSMsX0CNXD5N0ECmCYSgDONYIFIDD2akcpMD3kuVXxokeZ0ywPICOZWHUEA5Nj0FjLxfrtFo9o+PlelkeJWBqn2YGcFh/ASgPivX+6V+3vV3etoTLS2dPoJZ/0ZNcGQEPQzxVIybMjqcmKxQwWhPDQ1ke5Dy8I7gsBHuxb3V76PJpbEFfvSNcItyFjB3I86vVr52AoZ+UiSZ2wTG87MvDCmg6x/mz33qjF/PD8xeOPFz/aO7xRbk1vg6fsNdf9Pmd6YP2IuEPQ1do0kmWOkss1GylshpNIYAzPk+pl1av8+NLs0uM1+9EEQ+z+GKcdC/UI/4U8U2dirCANfnZ/3j92q1L7smjmC2PV77AIAezfpdzvmO3Pd8e3t3t1sbRmr5mzIXsNi1907CnFuwgSASMl4qCkOM5DQgeXiIiej7HxU+9/vQ4KpoF4rHwENpiZr0iU0DQFDe62EMMBohnp+BIHxRXE38VPGjAmoB9lTv7du6JYJzlOGr5rfKCJyomvLv6V88d9caUEZwNRWxYb3CBHN15JpqvpXhZNMTJILQQVYlmUDoeYH9WodPPv09Fpo84c3f5bQ3ImC8i9zuQ/iAmPTw8eDC39/zZzUCVwBhFDNempFYVuzIbFNSKrvVzr+afqZnVven9Axw8LCb9VBoKwRXUy9wIwwE1RHWL7vIDNMPjFiYCBLCwKMaYW6BoROcM34RdCC0IH7QVe/2II51SxJV1IuAhwpCenFjf6sUAcyRvyxCVIO+fFmvK4LKCwi/3BcEEXH8GO7Uomerf5SlfXbDCMHVnKd7IEKJ9px4NRwAkGaYuxMCP8AYkMSk1FSM8KumF+qHQAONBkJPreYsTOHdcxmOIKsX8RAKODVaC3R/n/UPsyLd80FDLABr5gHmt6ZfhvHr1z3iuvabAWUMV3NWrBBUH55fWl4PyPQjJ8gWVWBHYwzFijWZu2JyuS2ve65oeJBstQTc9DJdAb0I5xtHA/rDAjgMY69mcnbm0X+ABw3rjxY/ml9ui6D+ZfMLT7PdGNoDEP7fayG4mm6e9ECEfmBcvFKT1SOgM4vODSKoXVvUQPpkGb9W/ej5efWTSKsVnYY4gp1hBVQq+nfuDh6aWwex2665ct+ur3vVBDuA+lmvz+YXoU8v/Ogb4Orz794PuUABczYwLjQXZqpHwPYh3HYV5vBwABUW5IJbD78wu3wPwidVFYKIgrMCRucMumW+fmU9eE7Pxu/SxaGQxfUPyRPu3tB2MI28J1r4cS562b9h8ys3q6317rfwEMZMVkI8FaOmBCakXZzrDgv1r8koAB4iCFgCQW4aZ+Rbi22edMkY58048ci9IXoPN+fqjGY1eKxwdFgwXf+YxfQNsYBQmyIeHzVfas7wLWG19V6l1mH8agiynwLWVPRq3gtcAXmxYwrILxXao/YEICitYkUE06KNlW3oIfy0x79F8OlJeUA3wZ7I9v1xuWr5pyF4eqrwg6ljmk8/S4HdmOwV9I0Quf8op14i8e3p52H82ih43zyA9dvPZbYmoyMc8USMLkr7/tWqHxjlPQqsD7tpGcKP8BLg3oh3/u8/4pe3hoYG0pRF2oIIcvPMoTpjpvRvs8H85IMAtHtE+HkAorCDAD4+tp0vGb+MYLvfbT8FjPNxeEaOcssLFLBNR9c8uvypeKiFgf0x1QgrIU0NbDtd5MNwe/UQfNqaKPw49YQO27nDB/RtoXQxFBL8OfoHRXPTqV0j8MR9Tx0XOuu9fjIE/MOccajNpDrrB9JSSwTMduybwIf+sSNoIgquqRj3AT1Mz51h9BjRRMmpgSElft5I3j/USPEbdj1M4wfjnhu/gGAoQPWlFIjgLJNfF5DsVjM4O0PhMeOn9tWshLVVI3cd1biXG/Nreg3YBdz9Azf4upOTpVVgDRezH/03S9zGdk9ue1BXrh2rT9qjYZ1akmsWvTTqXPUDgrn0BACBIDp0EJBID9D+pDrE6yO42zuuVldXSFMxzKhnVtGX43kJFT9alxa/+L4/s3CpC5pKiJ9ynd4lZndLUSOK72O+bCoXqJJZq4N1kwqaCtwP9GxeG7Gen6vRiq398/BD76EQZCACBKmsPEqJZjh8obF08K9KsoyrRIQfUSnSKWT5zAKFEuP612464nLzzAb3o0BMiGDcZ8eP5nefeWJW2QBZFjhnI6yt6eONpX6iU387TSCo+A3VXub9+nHvsAJq3yu1lQjG35ExQ0yoEwhghLnGX7/4tjT8iBoSc6TthvH2uI5W/+A95rQLAg9vIK57UohgvK9+H8+k8VXi6lX0b64CWt7mpxEGfpT4CiFWlJpKIx2j02NkhNW7kqu93Nk/Fz4O7wakGQaCAPLxEVVTaSAb4ekJLjm+sj3/tLUdY+/loRuTQex+aRMnhKPdvcZNB+xBIn458lWomB2lXj2eHmE+72pf/ctFjdkAtqkYL9v0EKx+osyEksrSQXY0s2ynRitVj+cCGLlA18CPH+uBwYEfEhOeTgKCPBVnfq5rDMGp/WHSXD+NB2GbarbY/N/bPccMIHZIc08ia0yOn1Re3es6naGHnw4e8CyHMNwVv2KA5ypg256f/UAhiBgq/7tvXKcnKARhbr3Nigkb9M8sHdkMyw+M5rBQwE+fwmUXguqRxoYheklLg4iKYtvfN4wo0EeP9HYbQDFZJHNYzW+unwdu4WhU/PKRQV4MaxWQbcCec3TlnN7xNif+3QFArwlL4YRYPqYoa58QzMen+YNIssvPe2eWjqend+98G+LFhXZJAEl6hGGMBSA0ApHhvuUmoTWFIBtUgR+7iHSQsePXHtxWT6lVw76fip23oeLBbQFZTbEXTndS+FGl6ajsNiN3d40BXgJgNcIOWkYw9zXz99xYxMNl84PGV11+u+CHIQShehcXHz/itADmBoEgazCsi4QCYbPQvrURbT6awo83VVtblSYifgwN2nAkuzh0MuoWfN8BQwzbbAXqzH4X232PyzzkqQ0eiwBkfWMJgsAPk+GVXuapsi8o/PzA7f0ABISBHwGkT+iNCoEgFJCHoS07wLLXxxw4DQHIZ3h+gce1EQQdWaQDoOqp+T7fzATKscjmVT6cn37mRyTR68SDDXdIPrMNfx8D7OUM5RxXSwjuxDDd/8WAfkcE0cehchv38LI4J/zmJ12Gx/v37945hP/+SwWkSdaeMvTI0VGvRyzGOWFz20zV3cdC01j4kYMPGkN2thA/1CcI2/DeQSb7a+KlngKR/2cceSew46fgDG7JvhnAmoCBC7dAAXt+YD1erHZTyPBya6WO1ojbr50darKS57c7gu/fhwZmBHVcDwAMHWR4gpvWO2BxzhlPamYghozzpiLgfAqZDLAWcdwkbzuos65/BX7abFQruIp+5UxpX7Jcpf9Zu37XuM4tuHaaBAzCseQgDG8LBVIkMSasCUSyVQQXEtGSYguVj5DCjSCNmxAC4TX5s5+PRqOZc77vu7u66wuSJe16pb137vk5Z47gp/JLheCcNpy3MpCm3rf75gyUOARZN68q70pSsOAEswhZTFxWL0d++9m/gGDYwPhwK/j4cXx/fa3cOBIS5MOtzag6Jz3CPB6j5j7PD29RjyPHrjhbI7d/sHxyv/2bnowjNe285cZJYy/AMEDI0r8OwXYP0n7ut5afCcEHAtCR3PY7qhXMKs7M7ByCTrMiBLfDzznQ+Ti4PQRAh+B6HZ/xnTrFyImDIfPoUW6/Hx+rKBMn/viYZwD3v8dv8dyY8623pzg2UwD0CiDApGhPfqS3NUTgibNZC+uuVNpO4HnAwSsk+Mn+4cbYr/zi6Ss2b0Wl5P79PLyxBAh6xERykGduQLkPmQuCSkY8892t2cbxzj78Dg6Ojg4Pj47iM0BIV+xO+fo61wijL5KdMKGFIDy+ixICY0JM8+IC8TxI86B2HcZlbeajBEW1f7J0Y+1EDSk5cFhKyhPH96OQC7wzz36d7pqVYny52e4QjMSFX1UWQdKbmdPbbPPhDEPRerLOAcy8xDbU+dgNgogWY+cPRzzja4dfANAPgTDAJ4soRwwI4vL5TYUYCd1T3v90uVVistLbM9t6qqro8BMfL08K9pc2SLJIOz7cevshmlyAIWvSQO92DL9sR3dJygg55M4oRlUanzX65rXXK+8FfApBUGEmvsebcwgiFWE2DGhNu1/NkwB+eD4hSBA6+DIAc1QoKxhOeKzURQiyY8EctyUy5cKuIq9xNix4ZE2CsXRlT0Y8Jx6I/NqRTyUT7n5ZpfBeVrt0QfDbhbbbSlbK9bYDn4t5Pp0FGZ3yFn5KUVzxQLsXtdWtjlmO4z5ZSyyeevw4O+Fq/wBBRoS5PONx4PTqHNQHkWq0EbBGE9oyDpyeIshRIgMAtkrR09LFgl/Oenszx4Rfm/vCJLSFniq5q1LOFARb8PUmTuxdPrzPmXWz2qJMniiQFSQEnZwg0r1GNnvwkwX0miGPw8Offjo8rPATDG9uHIJenEGRGiH81KXnjk3V65we2sJGl31q6lfWqdfn3a6c3e6cUv+lJh742xlWsOKYLWB+dYlPqQOyLRJk2qKP6npp/2YlIS0Ea04M395SuvsQFEFLA0uj2C+PM+UjoBXPOzqahiAAuNkwH96syJH57jvGgCMYxmMSy2VqgI/6jmv01YefMmQA4qF78voLf3oAVG5OWEAFH8Bjs7QWudkJ5iRIq2lTMdELTnIm0GoSzgJgb1gp8wDbuSr1Rhjy5kFqTf32LWC2efkIQCH37R8Bv/iQE6YdXK1WmwBhMGRox8ZQ4HrB3O1pM1UWaZS0tBCUQxuJ9c6Dn+e/FX6M/WiTCMFK+M+1QF5l9nL78KuVvl7cV+cpb//eubWdcWekB0H2/tRq0nppELE0/TGygM+fTwFwbP9oAQVAQTCyYdJUNWPRWm9dPi825eIT3y8SFXwWBEb943kApMSG7ywHALzs4lU/RX/qHssb9QmpLjzgmn4VgLnRNgKe93c+gQX0tXv5FOIX9CBIN8yiJyU4yAX05fM5AXn+fAp+sIABwek4sNYGPzrhDVmCyoN7W8PzQFA9ah6aIVi1WJ3UPtf+ZVeWhTMAEWy7YoLTwq+nAIP3m+EX+XyFYKalOvzael9dxF0nTfYAYI+kpXw49ftKPEA37AStsRVkjXAKgHTCbSYsCMbBdKRmw8qDcfdmi6fslDMuY/gxbkL2Cw9BCHo/dr79q7dEzjpVsST/xHPfbfBTmFTjStX08nRcS20Y27886HQHQPBj94dgHnFhobHdQFa3HikVcQEPOt4p9+traVBkHmfCR0dPnwKENzdemiZxdbUKpza2eO5wJQ8kiaA2EyYE69ydaF5UkGA3RT3a7favN2DOpqEz/+CAnWszBl8WYG5/b3bCYknXtZa936OacE2XFuM8bffucN6p5K3ydsjZCfyAIKgJMYypkSVxopH7Vgj65LBbwOyELy9PTpbLFx+Pk5PLS6YjXpomBFcrRIGyaLCALn8hEYxWoapXilHFrY48ZbVkPE+8mG3wa+d1STrI1AlCQ/DLlrv+xfETH61o05ssz8GUpNb8CMHcF6s4QBHvyy8Xc/V+HYItwdsD9OqIK5GfbjgPboqiVcsvHF/Ke9FQZAn4CYLv339xeyyXr16t17CDGX6EIKflpDiVx0rxs7EyX22g5UXTi8Wvv/JG13ijRiNNsjuVtnvut69Y4IQB2T9OuGwpBZdrg/AJIVPvN2UrmO2fs6M41JTn69yp3+4BpUefL7bAt9qfmmurZHmUSeUYzbVKbry1fg4/8pwFQHfCBwdv3gCAL1++eydH7I05WsFwwoQgAUjdlUdbDlEB8sLBWsZ2+hYrCO6u1TMd27++aFC8Up3bpVEYwa++EpJEUUiCE11XUo42w7UlGJHJevDT+70F4P5yM20y0uZBVS3BYSg+b9VDnXK+FYC1FrjZfP01APj992/fEoAOP2cNBgABQalnKeKbOkhp1dJVp4qKqJCVQWX/AM98AXc7PPVwTmJkwF6j3cX6MUkM+DGNwHzjFPxM5arhh47fi/drbNfRfhCsfdKpfKt1wlwNqnV8UgXMh/biug0kmATBg4Pzc8DvxYvXry8vw/ZVCEYDjxAESzoK0sEOjIQkWz+Mc/aFcWU76cL8UscCLheCE/zoonPw8pCeiKyQLGCFXybLtcGCAyUTpnqW0lky/YWtpJH1wUdfyZvlbvDk00CwzYXraKYXM9p1XJhScwhKPQHQc/hlG0gXzJKLIsCvvvr22/X67EzNODw74MeDw0tU0/KIL4B3ehoA7EEQig94pBZneKk59aaubBUGUpA+B4AOP+kPKPnI5iDTTSsMfSiTJanqiHsQzKt7p5hFDr/PPzcV4P0h2BakveSS86/WBjKeotCOtkFyhi47X4kxZgiCA3Nzc3W1XJ7cHldXcrdMPmQzCUrOikBFUPAL8MVxetqDIP5SOm/9P11q7T4nqwZWkPvSHRgjStQ0ALn6y6tyDj8vXY8pF/0CCttq/d/egnAXe+210LtsBW9j31y4D8EAmKaD69C6FGZI1RpDEDawwo+FGDlhgOvi/jg786SDFlDwUxzIEU4AiuCLzxEjCoAEHEQkQ4tAzjsDMBwwbFKcH9QEJYsh6+/d5V7xZeqSQnBNygWCn7dAs/PtM5n6SvmjqDSDbwqCNX+WsVv45t/9IVgdC+movChuCd0CghLkW5J8OV+GYNY6oAWsiUUcbcYbUNSzKwABQSjKEHiAXnxerQRA/hsOOG4A2EyIYwCGGYAcAjo+BgRdO9ElKPsABCzaWpoDSWNU7R5OVWWr9ZpaFNnPlqey4u3Pa+m5C+0DQ6lgXzesO5bcEm1+AwR9ANCltysEGQ3WxSvaFcllfO6C3dLVnwT8zs6yvawQDLJW/J5VOgKAYR0BQUSEtH/QWwg9F8SP8Wh2wT3XJelOjijIR2Sbk+kPvUIMWTBIZ9puykhyN0MwM3wyBPFbtxdlpsHXa3osnAuLJva+VlDRn2sYE4KaEoY11MnPc/6ICFWYkdPNWqoqw8gKVrtH6D19en7+3/vjl1/W6xaA6o3QIa/XAiIAyIINJN/i2aFDjXQEEHQBzClCKVWrfZmsChhsX7nAiVYEtR2XlhgM+LR5bwuXqRZar6zSK0vn18ylmhE3coG1BVjK+SlSkcyH8MFqjajrhOvDIcjvfFlhlpwUBAUZxXU9CMaxXp+cRFaM4+XLiwsHoCcoMch5fb3Z4APgi38BLsJQe3kph65qIt492nnqJHtoojMRk8kQT2csSOhJ4DPrxUyNKdFhV+5JP4lorWyPQDC9NSRDsFctHIv7LiBsyMXE8yCY9wVDnDyHvjyR0EaIk8kTnk9ujRDzvsy44L/9pu/CAgmCASJpIjwtB+zfF/fHycmrV6sVeicZgnyFcMaAYNjAAKQSEcgbiUIRdgztRNm/fEHdKQNY2ocHR+wQrItrc5zY4yyi+VXlAUYQrO63T6DStXOxjl5SMYIgy05jMv8CSuzYAvzwVKSSjKIiL338ljtMdZjT02oBceLdDbcQDPi5BSQIaAEDfqzztfA7O3v7NuwfuyNXV+AQ5tGlPD232QQM4YThlhkF0iYTgPG3MHVxvkwu2igoQYhBty39/pyO6Hn5kZFOgnbBVWnLsfXLu1/a2Q2GaLvADxBsfzqeJVlwjR2TkTmNOXJ/Mzm1L1fk+0BYfIZmc69QUxMSSo33IJj7u9mlBvzOzl6/hgNGd+Tnn0nhqtkzvgroBQTDdYcFBACRZPgKaMkAQ3uwrRX6T92p5kWEOQ5UHAyY1kVdWtWgRA+v4aX/hxFce6NDLfxccYZxXVZ5deh5gby7D0DbKBQJPhyAajJBZa92O9wVEUyxOCHHg54NjxIShx4+5IadXtBawYuL5ZIWcLl88+biIv4HtLTohP3reAW44bCBAcDNJixgwOnJk+tr/Q26JVCy9iYdYsMKTai5YCBBm3xh63Ae5BuwaJGUB8+VFdyI0uEQrHIevS5FllOp1PleVk74teOfLQS3k/0WtCkZgnPlByny2N5ZPQj6PnNCEFJGfqLFHhxDMADhoMtfAVbn50w/GAH26oHVjhJ+sIcsyETfhH8DbLAqhrR6BCfqitpZpK1N8SgldQExxnrwDFwvHXQHRM5uAXV2tCkTI/Yqa1eeumSBSL2aos4zA869kP7oZ1a6GQ0vdQAIuTRAAZd6biKC+VY2mcbkbJWZee/XrHiktUpxNwbuvMhxeemGo6/bpiEBqffvBcDl8t27NnOWDaSmAhmDsIAszsS/6ACj9kd9BfZLoEitSqXG4LWzRFtEI4fWTk/qQ8fX4NkwSQF4WbL3GUP6B662yZFiFU7ppxs5wanQq/DLACOrfvsS7i4ACQfYQMSBD++JMA7wutTorVYAcg+462i1NpAQhEPKVtBJCX34HR5eXr67P3788fy8Fm9k/6SvdTc/vKEFxBCTd4zpRtErAcQCfquVIlOqcrkeDQEaouo4D+F+Iyyh1UOY8uxZ2EtaQPaTWFXVZy3i8SSEiYhowNtElRn79eHn9b+6YiIrEO7Ks1/AquBAOWZeHEhRGjf6YwAq/mFZBdBSZ7QtzBCCSEmePYtLFAsXwgJKATUu+cXF/+6OSD0EQY4nOZFfJAayYzhd51IeAUHN0UlXMC4+SQyoFqJ4He5d03rKqp1IAe53TDxL1557LRVs0F2zbqBZGlhDJ3A8eeLbl30wIk8j+uvUBqk2JvUJsFLLyiseW/jttmNgwSyTAFQ5Zp4bbiU56ioHjwMFQcaCKliPHbHu+QBCXKIMwA8ffvh4fPPNv//+/TcBxnmRyHm940HVLCirQmGBSltq4aEcA4HLgJkYMyzHEHxhH/FcKLXydbMgCJwzAPjZZ/EK2OvODSa0Z+6wWaThmdG5gFeQA3ZKVb51a+mLr+n20Psw1fplCEovyyH4sE1KCwgF4TP5KJyInzeilAXMqYKQ3yY5L97boJtxR4wbohU/x6NQ9qsF6YuL338PAP711z//bDaM7khTPTrSJpHcFRYEDw7+8/EABF1NAeVpWjyQEQClOwhukAqJbxivB9lMlslpB9HDfv784CAWjMU5YERJ0OWuD+2tbkwBSPyhXIaR9KQkklv45agyk7Bqziz4+ahpIMVjwIcgZgGtKj8kSzPPDee9E6IfMK6jVJvkyqcg2HfGfBQhf7aAf/75w+3x4cMff4iixXGl/zN3PS5tnl1UJhQ/oJRQ1xZEBQyDERJiURQXDSACCSrbEoDBIBlakeB0uCogQygCzP/683o8Pfc+7xPbJWntM16XxKg2npz769x7FxbERisrzY9ndxeXnzUI4DAlw/mCFGzhJ/Pndu+LdfT51J/CoXFwAwh+ugD20+gFwp3wAQrzjJ4BGWTgTa0Ku0aU8y1OQx0ndPuZ3cWgzzePP7Y13TPgKLwXGJCswsFp2hw0Ggdyn1x8lxJOYkI68BGC3jsphiM+KYPPmgH2DFgqnZ0RgIMBvT/CLzJgv/+/cEw7LQYEB/qAxOsG+VMV5yJMIePia3HZdwLHxtHpZoABQNZSfHcgNr7xUhzM3j28mt5n5FsVqRl8lhmGly8toBlWhS9KEIYpb2IMHH3AUc4UWU9M6BPSo43k9+X2P/4AqymThZdJFREPwZcvLQ1B+Om9mh+IYd8RiQ3GnHbgAb59+++/t7c5BtRWzbW1CMByeWeHgOHlJ05TvC8/zgczURJGBrWP9n3IgVF1Mz1tv49SMYqQufFXTBjFroqB6VEzAJG1IfwgFeO9T0OQky3y2mcNrJzElvkpz39imF9/Hd0IMxQRA4L47V2qLJe2PLILjhBkZIYXMC9ViAIvz4Dd7vk5APjhA8Dj4YfLYHB6ur9fq6UA3N1FEAL28xDMybbg8SnOpbdJ+IH5FNKkADQPcHlZRjh2uhgspf2OJhhCVhphjilP16ZJ/uYlXxKEePfGJ29SWayAF0e1zUzgPKSLuX6Vv4qGE446LSEaYRaeYs2TaWVonpWWBksKqHgZ8wEJKqVWHOOftdFA8oXdIYLgwgJ8QACm1ZqbiwZ4aanV0rRVmmCDjgdh5DDFuTS9+Jn0/egHalwwvs5GC9vXAYBmbgU/jqsDLLVTnrURpqnJgrAk3sfGBQmD4l//puWt3Gsapa9qe9I1udXericUH/kLcU3TOA1KACBYD7VfQZCeie8F9hyYj9eKXEghfFQGevj9+WfKgDbk3Epzkf+sPoyRv1j2IC+Q0TA8SAUlTFsLggAeOBBfLwiiW0XGGhHywYH9hFJJ0CsyIIDImN+XMr2kQQbYFy9zoZxgme5Hyk2ziI2fvgY8EQBqHATzPhzP+ubN6OrA+6ELH3W/rBg8DkEzwwpFfBScl61Kyk8WjSIE36IZ4Qc+Y9umFILmAWritOJhQsweYYJayRsfMYM5kcqmF8nbPqUDANrXLi/b82GEmdBBmgb5QT6KVMxvv1nQheyjLwYCgIp/MdfA62t8ftDnBOOCGh8Bp7VfP/xjUvC7A6AfsivUi35H343D5VOAEMHn5Uf0DekLRk9QAs3HpaswwrEUR1+MkwGLECyV3r2LAKzVtrfjYDiDhowwUyo0xcwZymOMtw1a/lGEIUhKA3721QcH8DNjohpzIQhKjpBDosYg6HfB8/X0RUu4VPkgQ48XcwxFFTXB5xs/JwrAqOXPBd7jNShpq7clAooQ9LVoz4LeW/QRcfElg0nywlRvgnFxLgKO/eFTD9BCkHZ7errZ3NysP5y1h1Ovb29HcPkcHx7lx4UF8+rs1vL94ecYkJAFCV0C0BfrsNtudpahFaJkQZB+Ib1mjln3vSPcpB6TX0zRAJbFGlU61TGdu6C5gxMDYFyllO/mHLVLOELQyy8FsgjENCuY8wf14tEEQ1fsi//2R9akrNvbM3fAge12ubzoztxcpbKyMj29s6OgxM7RkWUHj48BIkJKzGaP4eIzcGt5WQDULZX4+PV8PhM8tr/E/iUbG0jDAH6QO0h+pkf9jmBvTLWbKuqkPyVEiCpCTrrmTmOuXZ2Z2JnKD5lW297o3cKalUAIPht6CMToCzImTv3BGJCQAb0yGiYYc6NnZ29u/v775P6cH15egnu63WZy2m2bSVipCH5z98ekW82mh5o4jaDk5wTG5eWDA1zkQjwf1Wgmuw8O8AxwoN/2zsDE/j0MR5iS1sJvgBUhCoyqH3oX0/9pwuUxHXRuR8h4M9Q+AcAiBH3ZZbzpqcoJRkFpDoIoqnOzuUQKeRbki6lkjo+BxYAXFycn63fn5MTKc4IOfLnTU0tMYy4rDTPYDwC04W6tlocY4IcjUHqwAZj2iD+eAwldPAeBCGolDFE2NvDvQaUkjmNC2CIYmpiBfh1el+HwS8EY+VDDO2LNY3JGdygA/ait2Nk0OuX61S6fB0G+w5n9onHOQdDPmY69IZwYbfBrNM7P1+/P27eXl4MB0yvkIktKg3Xm53d3U/6z7pFOZ3YWYCOXAYY0tfy/pVTg1XkGTDmQcbHd13MYdaNch8CH+UJOriH8uJ4MozsZovjWLrwqsXoMeRwAWhTKKQnj2Y9TDb8U/BwAIwQ9+EZlQHWL5CEIo+LNbWw4R7cZQcnMf1z7SkVcTMQo9WJ/7MEA/Le+fnhngK+vkfw1CACCs7OcM/3q1d5eEYD1+taW5zGyHuJcAk7s6CEXOVBhjEXYeoZd9CiZ9gEAES1L0IrqCzOVyGfic14xaK+yak5qCM01XKZmOV138/ja7YkCMLdmDr/IOJZffXLqDY4QVDQX56SCBWP3SHHzsJfp+ykxkp/e3Kw/HBNomfEDUMiA9lwzwnb9/ntqgOkBNho24g2n28VlVZdSicAifATEyH8+LUMAwgekH0hWhYcINSGTRoAein8EKSBIAFqaWsU2tXly5jWXW6ctRznj67eDfjnwFRgw19uOSb7jDPD1I4uKhngYBFmOj6o4GRYzM6hw+smqMsJKupydCYB//WWwox8Hbwx/4Pn5UqnXy3mAe3ut1osX1eriYvnhIG7GrZ0dpWFUQaaRJ+gIP8AeiSACEMdzKAw0mdAnaSjhEgTJjgxDUviBAf1m4OKSHQ8+Sg2+nNF9hAE5p73Y3T7uuI60Ty7t88XMlxSGHEjkWRAaGI34MJGRf76fmA8GvLg4fzj//DMYkAGZmWON4/TUcoA+AQMAVirWwG4tnbiPpiadvT3CzqrL7bapCvv97e2trc7dsVi709na2t7u9xFpt9u9HkIkmd8iU8JgI1Rh4sZXnwXBHAPG7IEmLfiuOnGi3zgi+I2rchkJgFw1PGkjjJFh7M3CojzNvhL81OotE62RbJKmRwjy8ZUVmwV4dXcwdIhJ54E7yL8xbkX5jPHnq1edThGA8AD7fXqEEX5zc81mt9vvb23t7Gxu1moAqBnucnlpyXqP6/V371YfTvXurK5agrvT6ffb7UZDEPRRM4ITz6vqK6FZ5iXRgjHgTz/x9YBHqIn/LIkOG7zm17zOfMUzlcvdTRaCxqtc8+d9D98b58dNFiGIgMTzIyGoKQvPnp2dnZ8fHhrP3d5+9502BsPXA1/gnswl4bexYQzI4lwMQZrN5eV6Pc9/5fL+fqcTHwMAFxdtNHqrVa0CdoBftVq5O9Xq5t2xR6zGYoaavEcIyiukh0kxK/nPe4cMQgyCUlVH/mPHDSvFcW7zU0AvC0CfEUwF2OOYYExLIOlLsB/9QKnhUkOch6CH3/PnSLZYpGsMGItvGl0OAAp+gKCZspUVPzsLIIREa2GhUskB8PXravXFC6auPXiNATc3zehWH87795VKrba0JA+yUrGiX7VaqxnISyWflAEAVSeJCRoZYCSpsefEuzRWtOOgTKyoiYpBRrvcg/wU0BsKwCIEoYMYzwj//HNcSg8eJAd6FiyOYAML+iIde2Z1r9WCDNUiXeMJz4ASIiA1A2mAFHr2Z7UYmNMDt93Z3bW6cblM+HkAzs2trTFwSQG4tLS21m4fH1c/HgFQhtyGxFnV2Xjx+LjVShkwjZ2lvgEDauenQdDLV1kZoTIdYYnvfNNm45knPFOPBQ6TMcJc6hRb1WNErE4IQpD9wsgVRkMcmRD/ZyvS5eXNDYCV4z7cGgzOwrm6QlKXx4uy7DSbeQM8N2dtTGlfCQBYqVj9ZG0tBSDqzvE7HR2ZMTYQdjrGhUpuRw70ErEYG/sWAbydyYBIvdAkR/7LbzL+JgDIKobGzdi90SCIIMQLE+QCv3lDiQLfu+A5XmmbjgSbadqGrUhW60gTMQQer4uL9RP+d3JiyRkDndUXivuKjS93dnL89/p1udzrSbwQPUCrn8ADRBACAFrq5ugoDWXoT1Yq9boFKca6LOfJC0zlXmpxAgNSN0Phgo1Cgq9t97yU7XGx3ZMGIamwPkJwvERM5ECtMoQhBrQ4kNwP5TUupIkmBJma4XN6vcNDK7Wtr3/40OtBkI/9mDkIwltEfYSQzYEP8CuV4AEWAbi62mhED5AALJfrdUu8IAD55RcwoK2MMHCmTOpV2caFBsJ2OwYhknsp7UMVoeDHop3mbfEN7g0wQ5Cn9P0+A4BgQVxURYzDgfl5dPIFZYC5D85gFs2xD0h85Pz8OVcyWASsGfk5FhwM1t2xoMUyc349dgQjPECTZaUG2FLUaQQcPUBAz/jv/Xt5gHkG1Pc1EFarx8fdbpH7fAqJJtgYEE2ejIi1PMfHxOkq1sc2uX8jAJyZweInQXGUg9mBfiJxsRguCGojEr1BD0F5g4SrX9rqe0KwmtV7gPh4deUBiPJcuiIbB5XY3d0c/xlbWZSbwgcAhIIGHiASMDEEeQyA9tly2cy2GWPfYSf4ScQKzqNsgXyoDhK6MOyDi+1GEW5P4RF+5sb0FH4//jiqCR62EsWP6hD8BEElZQhBzhegKCnqoQ1+1o5EVbQUzCrN2TGBlno+kJBBkR88ODsrDzDtoev1mLoueoAW0zL3Rw/wcwDoi4CWKzRPUhBkuY5GWO2hEHBJuKXpsbjtxxZx63AE4DeTBxwOwVEPdiiJAzleNgdBToIG0LQbKcbEP/xA0BF+dqkfBPCTKN93xVGcBQ/Q5ifMz6ccqPulUrWa4z8zlN9/b0N/UwAaBI272u1qtRgDDwtBinlEM+Srq5YrbLdlhqU/ZCsoK8RRtiWXBffUHaKxbV7v/lTe4NTX+CHcXCsIanbWcAiCB7EfyeuBNV3KGndOT+19zzlUDD4QgAiGUEfbn1DiLALQ1hhubFxfXxWOfcY8wCL8LHWytra/f3SUA2C5bB7g1pZ5fgTgfzHALOUtLdVqqJpsbzcaXn+tvKDvsUNvnVcOYtGjRqCn25hY+x0WC+d8xMmGLl8FgDDBxaXWmhhPnYYftQgGRKMOpQqpLB371MVa5D+D3/X12dnFBTJ9NzdkwKur83AuLlCIYxoHx6YrHB7+n7qrf2n77qJOYYNnjE7mJgw2BwqCzhDGRGw1AZZgG0xs535qhTiwA0KdYTXFNwSVCQI8o12Z/+6T4+nZvZ+XRLunDe4D30yNGTXfk/t67rmgLqyu5uCHg25u3n2yBlitwu7litD9AUgbCgAWCta4q9ebTV8b9N0QBA2esCBqLuJY6c4YX5pA9Psy03ogvmPS6YXX8J3SUWUI/wIAyv2aFbTtQaFytE0zAGJ0xNoS53vFsoGAYOg4rfgyNnZw8OzN2drqdPb25MaWlra3we3b7h5TRPWOWdnxxcVXX9Vq9e5ZX69fHVNYRQ9E9NUYPozcHj3a3d3YUP837YL0tn+//MI9nwAgAQwILixoMMBTv/DxYXka1FTJwzEnxqEFREJiDHJaQD9+4dfIkH7HsIlMKDx++WW8euHdRI1Dg7N/ovv4vcKxeLlUnZiQEIJaUhjTFaQw6uFnSQd4gAJgpwOdGJ8Li6IgTYPj4xiAbOmZxIZae8yrl5bwODeXt4CgGNRqgB1csIdfWszp5YCnpgoFAZBcGkaD8VCU9Wu8CKa9L7SAYktTxChd3AUora3RvXoBDpPilSqMiPrvirA69P7hR70sQVCWMJ8PyxlbTqy6oC/MWO/Y3mpxmw0kGEXCQakZSoHWjLPaoCAIaxkDEK+R1IZeNzbWjQvf7J3j2ocUPogAy+VSie4ztX9v64AFQB5wc0IIKkMOGYPsFYuqBZqWprJ//jkGoIdbCsGQHW3PvhsIDsgCkg2jpaUhBI2gJbVO/jcsTltWbB1hxYGEoJSdCRWMIskBo9dhFtCXpgXcsDTD/sjBgRZ56f8L+MFl4/Hzz3M1QAAIEh+oAQJ2s7Meftc54BSAgN+jRwa/ubmNjdVVGwDwowCygAY/zdN5ZpE0ZIaGwpYc4SYrqC6Yt3f8qW18N4v4L7CAApy5X5+OSM7Xpvu1K8PvC5ast/VB+D3iQLJEBBV81Wp99x0BeHT04gVcZgo/ZccjI7EDnr4aXyK3moNLzKph+7aXGGfGNUBRubAEDDXAwt/Hw+8mDjgEoIcf7Wm5rF6xjcZbX4Q1TAHQqFoMXijhEa7G9haP5TbWfe1ntoCGEBQM/1/4DcgCapMSIAf7J+jl1nqZFWRUCMEOAQ4whNM1i6gKIJ2wQWxkpN1WBIhozsrQnhUj+OUjQCzpAgSVrmxvd70vzjbKM1z8lQNgoQAiKiDEUorB73r7ZyWYOAI0AOIZdooJQRtsx7/Xw0+FaQUzklY3UY5w85HXvc9BkHx5W78qR3zrAahesrd/vTbV2jIWSdBqBYtBENxAdY0BP73pHoJnZ1ZoOTiwBMRHgZoNDptz7I/s7OCWNho7mdNuY0ZuctKIqzq0XuXywcFff52f88Lj9QXoFICMAI3Q71t6HoKaKkbs6+FH+2cfXkbOmi30ADT4saxiBRfbwi7geZFeiwtvfR3Q/pywEOMl4cJUxGqDBkG5YOXF1g8ZHm42Gw1zrRxL143wVCw87u2F/JheEeDoqFiG/sxs0aWDvrq6Ckagxo10hod3dg6j8/z54eHL7jk/f/0auXDvJlw/B7yxoYhydhZFGesOhx0coyrIU8gC4t2kbLJYMQY/63YJghbtpRz5my7jugUApBW0sNUXYvI9EZue83LmKr0YBL/4olSCetXy8twcFKyMB23KCN764VYBfqgK2nOxAwYALy7g0sLytBiH7fb2drP5IDgAHh9BB+t0Zmam3Zm5Olvdg58TjOfnYR/Fl2ByAHz6lBGgnPrcXKPhkxBNvvDRdGakNq0FkVKTJvy8O4WztVog3a5qF+GWkHdl/wYGQNshoQw4LMWE1i/emekhqJIMrd+3305N8fahXaUExIaRQiKqpnUJQT2HCPBZdBQBSvDcH3SPl5aqVbpbTQuzcAzYrK8fHx8dGfTiizDc2gIQX758/bqfAw4zYEWAjCnHx6vVUJtQVcGwS2zSRjqajlMXJBfRaUQ33izsIeg3Jt1SAPpd6oKh3DCv2AWbeE4egtYbAQTLZdbiJibq9VrNC1JSzdRD0HTyQwiOjTUax8e8dJBmIDmZno7hR3mPn34S8GP4LCysrrbb2NMUH8LPH0Dx/Dx2wOiCpDVAMAvDiiJiylLpTnLYnsvDT1rTXoTDAiRPvAsZnH5rUriumu76n1NVBgDAdI2T9UP0Z5o0rO1VCkGojWhWnEYqUioRCOi+Npu2/ZwDmKEVvLhoRyfNiOXCSWvIRYDkD9ZqcRRnRegHD2IAenccAnB62tywiAy+CRdawLSlNz6OkkwMwFhI3Q99cVOB8aLjInQMP1tYGIqWa1aSi2rYM76VAAy3SeQgmG7v1jyXLr90IITgwgItYLFYrxN20m72FT8Crd2+CvCeXbHxn01v7eyoP+ytpMo5sCMAUi4CHB0tlXqVYFCEfvFCAJTj7WUBDw/jLjDAhzYcLWBvB6ycenKy0Yi3O1EtQX1hW48oampIy/cQlD0E/Mwv2e7MEIDGkv/nI2tDg4j8YoFXa+gQhMqJvZag9mGEMFRZhiC8d0+OcH6+VDLpcBaKfe0PkZJUAjkPAiCFEWKo3gcIphHgzAxeNzKyvJwHIIiojcbRUZyC+MsD8OXL2IUXCru7sIG9aoBpS69Y9NPCIqpSykiNS5uWY/xHJhKqsnFXQ+lhqB+oLQqpBZR8H63g28Nw6P2nHYSbT/at3aMsy/dIBEG6YmvNhavp8aZiXFIU9lpNcyAm0CsLCPgtLWFs6e9OxzTy3Ds9D+DXaGjljR11SDDCnsIPc8LlcqsVwq9fDOhTEFQKAcDT00plfn5yEkwaVQHN/uV6yogE/cA6AQgI+s2cZEbbriWCytpwhJ/F5La5npuzem2MYxwoutbbpiVD7zf6811E2Tw/6MlPHC2g7xD7snS8Kdz0AD/88OFDlEBQEtEkiAaSQuu2t4fWXEi2wm/1gyBekY8AU4FzfQzggNMUxJzw9RHg7u7KyuXl4uL+/uzsxgaSD+sC9yI1TExgwY5PQWgBBT9awhB+lgVbtc/ee/RKTAY53pfukxCzgmtrCqzeBoJD79v+SdhafyRacSL14E8mUwbOwCCIr0VVNSesQ8V9T8lCL2R0NNyRHpdf3kSArtNBqbRe8Ltz5+wsFwGenNy9Gy85lAWEkpaPAA18sn4ehF0AHsZFaJDwV1YWu+fy8vQUch7MfzVVwsnidEYFbjhMQTgrjB16gh+1JLxijNQRfNIRb6kPp+h6Q1B047dV1R2ACxaNG/Icsne6whoTeTJhdTAGHx8xZONXM3h1/JwF/PrrTscDEJGcnxPJxYL5IjQUtuIlhwJgsYgaILYV57Lf2ALOzPgIkCWYQmF/f/HqPHmyuFipQC+BDthry+S6ylwkYT0QLNb+5BPAkHGgdrz7yRC+44gD821RvzUrjv5o6XCtraXiznj+FiQhtrid0cVHHz18+M03tIKCYHgEQUkZ+cacQVArnKGGEi9n8FuSDFKARTgJcnzMVKMVnIsLFJnJm+ba6zAFweuGh+Mlh7Jg1erm5tkZXGveBccpSFoDRAR4eQnwEYKPH8MV34RVODHRbIYxIOAXDilRrEOTIfEyaonn+aGxHPzS9ly63IO/c8s6IZbzxqR8/skxFD0E5Yq5GZI7gjWgxB2Zgl6tBjFIHAhFYqQRpedW63lwTk5I0Do4gKAbLj7iarVYNfztt+fJ6XRA0o8jQNo/FsPb7TgFCZ2wHYsArQcyP//77wLfkycrK48fVyp//FEoKP7rR2ut10PNGA8/jWmaln5uK0gMx1Q12tbWKGlMVxyZG75lAKQbJhUh/NTgTegHQXO+OIAfLaBmv6SKCgAuLxs3pVDY3ORNwRRIeETbj7vAnQ6z47Gxe/eOj3HhEX0SpDuQOP/hhzyRgDXATscsoLd8uRqgaWRJT6FY9PAjACuV/X3UBa9TVhgfx/gmCWaEYKOB94erb7T0GhD0u+n7g9CXXizmCy2fNq2GpeqbitsPDICCID873gLKDubfBq4WkCy5iU1Yhufh12xCy5kWCcxk3BJYQGkJaH8v4QfWtM+NwZ4+OTHaFm+mxjr5k9HRYrFXDbBeRw0w7YLks+A0Apyd9RGgLGClcr9rBVGgvo7Wv7ys8STLhH0vJJU6ZjQYL2izKDzemRXDz7ar4iJcFQnejKYwUAB6uSM/npl+ZXZRFhARjFZVCX6yfxYBlsvz8xqjnJ+vVlVq8Rs6mCHjJrVaiPNinYQwNzY4kugwOppGgITgwsLmJlx67yJMmAOnEeDGRhgBCoBdCN7f35dAem8AwgYKgr4ZF+uJsZyv9Q294BcurVRxxVs+LUzLlWtuStYfMABVmoFcZZqChPDTBL/y3liyMregFcPgvKUoTayvi34QA4pwarenp0MXjOzYfttTGEjMv3s3HUXirUcEiBog6As3ccH5CLBSEfhkAQHB+91Tqbx6hd/JyYR4G+jjQJPusEkafJBtr1w/5xvGdb5QzWcIvv+8OXTCPmIkcf86zvQAAWjLu8SDIQT1GGdTZv28FLnfCpcuqK5WZZ8wHAmdvbTRZjuSdnY8ADk/p/6IWT5d7DRjUD1366emAEA07/IOOLZ/h4dKZawJVywyBZELDmxgF4ZU6erHrGYcmK52EDPaK2URfnEwFMJPEaCKLqHj1apdsKxpDX/8MS1Z9y9KDxSAPiMWIUFfsTStMrT4MdqITiKlOV4BEIp4Br9mc3ZWNwfEKMr65MrN+Bloo3DA1iFGBMgiDMox6QFJK60B6tYXi+AB5ohYOQvoUxA5YEaA3gVbIgIb+OefhF8/av/TpzYvbBA0+FEjwaceSvZ6JYO4K4zefbMU2+hsh9Vnn2nOJKUt9Jd3HmAWnHaINR8Sdo2Vohj8wrRD88CcBREBAdbJD0oCEJ4Lk5KWUGgJUxAMsF/lzN3khGw9f6C+/+uvxaJ0WzhyiS7F8tVZXUUEeLMSTBwBUlHr9NTsn0HQ4kCUZPrDD5bfFn4ZK1BRIOaDVdQSHcvXIfLwU5+XKreCX7j5+dNPPQTDyPEW8AHtayN7+3IL+8JizIR7lfzuJOk9afxQEGRW++CB5DMWFgCImJAanlbr6CgeRWIEyOQk7gJTfb/RwPQJKasqeKsAHnaBDXxpD2R6WjSEfARoUaDiQEaC9++/eoXX9Abg1JTtW5KCKt6x77/36y1CpfxeMaB6GrxzxpMR/GybnzlhEBdCC9g/FRl63+Bj7U+ULJsziCt+3g3rLTHigcV+CKiHhz/44L9vzscf2/B4OPGbNtpUfiEA/0fc9f3EQS7RFpL7Uk0lhdsYrAqU3KQNyRqBTWSXZbPSygoEulBqLcCDyCY1+gBPVR705jaxD22Ipn/v5TAcZub75oM2tuwkC4BAI3t2fp45g5ZxCkA0odGevnMnJ+JDKWFhAW1ueczOdk8MF5Hm52dnBwb8FLjsAX/4YX9fShA5iU1JyzwDtAAUCP71V06EsFap8O6Sr4W1GS131M8rQfh8qHZWBD+q9ygEo8nJRZXwlffZcrH+TlrQLD0YZNXp479hVmxVBC0Affa3vv7wxEZGVlYs/VTeY00xV0aVS+l6piGfdHA+8ssvuQcUeY80A2QL5fCwUsl5gCUuDHiA4sXo/378cXf3jz9AQ9Dw+/334gG9D0Rb+jwAtlq8u5TuhmgdbIXaYr+n9FTdCOa9JRt8qVwLCDIEe/j1CIAWgrr7kc9/7Z0yLshY/3f1Krp/qf/r6xsfbzYfPtzY2NycnJTq1FMLvvgiIhnwZpIAcDkw+a6YiAqxNi1yfBO6Xt/ZAX2rFIDTIPzihQcgJC3jDDAPwt98k6oSWmu3v/3W6sZwXZP31a2/Sn3gxx+Lm/AqWLb08PCzJo0YZQ6+6Xmj98yGId3Rwi/OOUBS4GvPFyEqzcvJx3ffjY8/fDg62myur+Mol54mJPuPb2V711qrhTGcXLC0DZevvpJphxAX4gxweztdRSKIMHMpbYJEXOi//yYAuQlcrQoAbQaYBmGBH0qRcgYox1z9uqbeVFJSgg7hJOAqNzqFnw7cyvCj/0uJCz1uRHO5mbVW7AWlB8gyRHky7AMqA5qa0HNz4+OjxzYyMj3NUZn3eNz9RdvYCkyCNMqF7nSlkfbsGZopaQaIEZ0wsHMbG0MP8PffLeTSMFzKAMX/gUkoJYhC0AbgFIClMqRSkdMSXsANfp8eMN+L06vo8gxIxn4R/G44E//nw69fde/hTojS7hV4oGRpPqhXuW0dzBPz1HoXyVlAcHoa/u/LUckA9Tw1wy+gJ4+dnYMD7yHqdR4/8AdgLA8wzgCHhtKzhDRMgWu1336zTZh8HzhvQmsGWK/nGWApBGMmUgIg1zTzbWHmgRH8rNAa4UctHxYeEfykEc05SDo5lv5fz3JAmrh0lBd4kPdMd0+GtIcse1NKxdL5B1Shm83RE9vYkGaM1YShB5RHp+NFJHF+WuEXPVlYXkoBiA0SZIC7u/ETX612u3/+mWeAJQ/44oUHIJrm52eAPgdkAC/Pgv2SJh561lrhByfARMkGYLadS/Cjwowdw330kYZfC8GeA9CO4Mgl0//hqE7SV573gEK+xwbYysrc3MqxzcwIX0UVEcQIv6GhatWvDx0cYDwXA09MVA3yZfRaTeTKo6d9fr7RKG2CRBng8+ey06tibGzBaAaYw+/iIuT2bZRkhByF27UEsd7v888ZeeyKhDL9VDIggh/7fvI2b0BrFmjFf71EgWzSXZo2jAZjXQIkBOV7PvlEv1cJCQAgL16oGjwzGyqh+P4fIbiwAHagnRJMTS0sKD1LTT+LMkCsIiEDjGgIyADBA9QM8KIaGDQEBSD0oLFWX8oAoxKkFICnpqQhLu153gHVNox4LlWFEf55BEG7niSBNoKfNcsHzPdH0j0SXo45/pcul4jAnqB6QQkD8j04f4PvkfBgqVgkXkGQm/DjBm/aiBYwogxpNHwGiBvmyABLy0iyvFTKAJeWYgCKIGVpESmfg/z6q/we9YD1erfrM8D79/MS5OI+YKeDWpc8GDwGB0XlgScM9YI6AaHqMPKMgKd0MfxyADIMp+QuS9yPTqH3hI6F1x4Z0jotpAfk689SsdiAtkdULQSF92c9IIqRbtefEoSnQaBeW5OunwzV1k5NIMj29E8/6QMZ4NDQ6mpcAwM+HoDlPRDJAAlAasHMz5cywMeP8wwQw7jYGg3LEAL8xBdyFgIAXru2teWnHRaCyNMt/NIAbOEnTMAUgp6OoJpaResFF0ZLfsn31AcyA5Q2DALwjRsSgFX73V/NFX82kJiAMW0b3769s4Pjg/aAzOoqiARTU9WqQPDZs/8GBkHKw8M4A8S989IUOPKAz59znZ4HGTqdd5EBYi3Jk9QAQR3FffABPaC2n6ncjWdAVmT9RoiIQokP9C0Xrm1eDMFUY0Z0ZsSOvfFls2HUF+qkWEmLPv/TAGz9Xw6/69f7+ppntrkp/rBWq9f1TAII7RB1xPFBtJOtuino+5WKzEh4EJVkfLZ42u2oCY2nXTLA/xQt7QFKKWN7gJ2OzwDvG0sD8KtXpVlwvd6XmWXDaAUc86DZJLOH1GQ5XeAnGaQWHTkE+bUHD0jPV8Bxx45+lT/RIz6gqtBJN1A6Rn7sIwWINmC0AMm5fSsrGM3BNjZGRrgXfKLoXOOYDQEXcOp0JDDfPDMJo564P5RYtxtngGghr63lgpSxB0QPEK1xG4ArlTwDLHlAZIClEqTT0ZON3qiLIBeEKVIe89DlL89FI086VcIB+36RF2RNTH+HzFA3R8Tkd+F9zzyg9gmVEah31W0Lppz/qU1Pj4ygOY3e4Pq6FiL2xIxwYQYHweizIRQPzHJtPZxD0NfT1u90OtvbOQ21lAMeHdH/CvxA5X+7DLAEwEYjB6BWwMgAU2kOLj34z+QrAiPp8yn81M+RdpVDkD/rl9sFdgpn2qUWITn8rISH5CG6IxcBUPksqhKPt+vrGxvSnG429/b8WrrudOA9DigolOTJRB1K0W8RsEzht7yMq+lxDxBE1DQDPK8HCPgrAPMM0IbgPAOMEwHkt8gAPQ0/haDqoyoQ9a2qkAEwEnzpq0Qaj8BS74aPonJEv5aDzlfUPfeAKuABCLL4IPxQgujuW+QB5UaQkBMEgFtbqQ4+b2Xi/eIipdWYiWE+UqnwGmUcgNvtVA9Lb2aWMsC8AMGo7vBQShCSEO7e7XbTHmC5BAEpPwbgkycl+KUQ1JBK/ybw4vI/j3rpW/leQjPdGLGw4++z0PtX0S4FgFac0h648zxp+YgsGPGAXEInANHhQus57eJ9+unWVrM5+qUAcGRkcpI5oJJPueOLea7e92AGiE7e9es4sEqyKbUVxMpT4Js3nzxZXj4vA0x7gDz+ygAMRcE4A7QBWDPAOBHAUqgFm4ef1cu3Tz4/hmaMekXCUNotBKey/WyNK5VsmttxSsx/we7kXTIAc0r+RfmgJMEagNUDylVgQtDCcHp69MzW10lOsApZhF9/f6VyeGhLEHw0NQVpn0qFKz9phVyrzc6KaC7PBuJwoFirdd4UOIXg0RE8qfo/DOGQAaY0/FILppQB3ryJBhOBB9YkF/YtKPV8dWrWA1KPUae8mtV5+Ol+sEIwCrZ65c/DD48eeUDbdrEQtVRUhZ/8OVV6Ml22vHdPAfjyJbfkxGRgR/gtLLAE0QAML9RuLy/X6/HG78TEoFxIOjW0sbW2HhqKJMlj/4cmtJQgCsBu12eAnIE8fhxngKWl0IUFqkP0nWN6Y4qqWaRn+awQ0OPZNIWfEg7SM0NaZpQgmPs+SQN64AEt6OzXPA9GJTj4avYagHZvt69vZmZycnl5cvLRI6uPJYr5hCCmAo1GLq6LDBCiRvV69OR+9lmnAy1qMfi8+pnBFy4vYxm9JMWRToEPDtCE0ZtKd+/Ozr5NBhi3gvAi8bfwdATn4WfPnKlqtNxTt1cJCDjvAWMNBQ9BrqrnJUcEv0tow+QeMNVPtZ+xCrYkLFU4WVnZ3Bw/sb299PSWKBfYNU3xg7IXwUenkz+FqEOhqZBDUwDYaCwuxpsgkJPEmlJ6E2l//05oACCCOv0fqu9WK+UBlipgZIAlAOJiiC2a9G/R1/fzz/39t07s36eG+wJpWGSHzzdQ7Nei7RENyXnDxeeBOZdQAvyVy4OfBV7qDzUEoxDRJjSXMQWAm5sbG2g2N5vXrqVNFv9nZzjynw8OwssNZ7azMzg4P+/nxnxqx8a2t+fnfeovu2zIHTuddrtSGTuzw8PXr/F4fmIAo5ymYQny9KklYUFNARlgVITEPcC4BBkeRqGUApAvQD3gBRMYCrVXAWi1slKzAuUlD6jClr7d7Otgy6BmT/HKP7tz83YLmp4XFh1x8B4QNTB0PplaY9qBVvP4ODZBUvjZP7vSkaxsL8SLIpucrNWq1XjfAwexdndzzyPqM61jw6mI22emp7aePsXFdAEiOIVYRUIJovnf2FiaAfpNuDQDxHnEmBAGkpk2njhCFLPgu3ULfCKBoC9JpNrVlrQtOrxMR04y0K7ggwdSksRFiW8Anbaz/+mtrzeHX1py+C6gCHbQA0Y18NWrftaRS+zqzfSZmaazzU2BppA08cATAeYcMkscnokzwOFhUK2iXTgR/2i3l5bwk6Lal9bQuPexulqpTE29fn10tL9/cIAiQgHIHiA9YOr/vv7aZ4BxE3p4eGKCjScfglMACgRlXiJBmPCLPaC9D+K5fkqwyi8/ewhG0w+lcx1DnJxVtfelDBjBLxXrsFNg2wOE7e0JAJvNly/9GiZvBPMP398/PS3BmvNhEBR8SPa2uBgFYDy5OzuNRiTJSyIqLqMzrNv1J6ubBaE4ECMwg7EBmD3AvAaOMsBXr+IMENNkZrwp+DwEcVtewm/aFmEzOodgid0XMPuMNwQdgRDUrqDukHCqcuwB7fWO9wNBXXCOyNm8zSjw4zacSrKpEJFswsEDctZhSxAFH94yW8T3A4DT0z4Up7a0FGeAaG+o4pbNAdG+RgaI0M1cUnuLUS6JGtoHYOySCPnqTQJwKQMcG2u1eJ7HXgvlXyP3gHI92DalOQ+xhcfbgM+LVqYjOm1O2zWm08Y2V1CEpaxXYN8dAO15zwh+upfgaVgMwayC752ZZIBRvsOql9QEAWCzubIyUDD0F9fWqlVpT+cZ4KNHeX+Qiqit1uJitarFTAl+6gvV/6FkYQZoc0AKEp3C738KwBIfEcer9UKUDcNCwbDwEw/Ik4/e/xF+mge+HfjOgyCnKnaR6awI0U0APdr07gBI9r/VwEohSDZuyoOWICx9wLU10KlqNW2zqGafQlBe8cgAtTUNALKR7Y3S5qhkY6oBMkC0TqI2DAgMs7P4yYv8XyrFKwBEBigAtDmgeMHc/yEDjPuUExOUKGYIJovRe0CBnwAQ8PvwQwprMCz68HvRfsf5oZj7dClRwcIPdkVWg+w+lILl3QIw1QrxHpCaqcwAkQPaEsQCiNkOJxysfLkDNjdHboyEbGSAEQAHBgDogYFWK9d9lgwQNXIanAVkchdzaengQBs75/s/24CB/wMP8CIPSPihBxiXIBjm+eY7wfd/3q7GJe4ri9oKLZCkxbZpwSRdZhNLwDpaGB3AxkHEsBP8CmM0hTqTAlYhJCAIRUAqQEBoMKU2+/duTo4359733m+ccZd98HOs82HHObmf557r/yYsu1j8x33LkBaS/Ys1QO9+q+FHLYvSPnU8g5znMlfGAbAEv0F1PQbhv1AdoQxCwc8YuTYHpz5I1EGNe0BevFDiIfiNjkK6yAPw7CyHH6BH+CECjNPDnuLU6aTOmTDjVqSZmTwCLDtKvw+YAMQwpyAY40CJUn6IAI+qZvJQxcwhWO6FGPx8/pvCD+Ar5bwpOqiDrxyi7Iwvg+CItrj5l7DFnVfnO8cOR/66MfO2+E/RnxWhc+uHCy027sT0hWY021Bc8fYPLrjbTQEcoTg7WyY51eug9VdFgAsLrZaPAPtZwNz+1etTU/v7rdbS0qtXMRP2ANQ5Pq7qVHNNo/42vhCvJpz1gel8Ff+l9b+UK50PVWqz5vi4KQj6HKIMQZa0c/pqpQW8ihOOIg/RxlVB0CuvexagL8FEB+ohmB5AEPMhHoCLi2treP7Z2XZ2wJ1pt1HgLQEIS7DTGqBBCaNI+/vNJsaKLs+BU/tn+4BhBVdWXr3ysWAJgOfn5RQEUiPK7NO+T8qCseNF1WLxJWa+Zadrn/Cnn66vYz0rvuJK13blpRlzyhUWMN8ENhwApYUlVU27/DI7g6CWtnI+OFpAU8KPEIx1vEZjcVFgunYN9wCCXNDSaMzPd7u9ns2KPXnCToos4/b27dvgt7Tbj4qn10N9sARARHAo0GApxGUAVGHa2z/bB4xuysoK7GBhP8i/VAMsE2Lr9WbTwJdeqT60XanExqDwU63EpKfSQwjSLlYt8jL61gdif8n6SVBhuGKzmeNYVdSsR5QtVPkFz0ISYpNYUQvfV++81fvqK5SmrdZnmS4gyP6nn4nF7c6Ohx+fA/IquTUvXkQLy2wyrQ8amDBhjC5Ive57H2Xn6zeByP4RfmQWdjqEoMWBSEMGS0GmppaW4AvoEXwZWhAsMwDz+C9qRJc0DfT5jo9/8cX4eBmC0j2oAiGt4UWuLVz740clB+nxWvkGulfcDmEbIrwoh1fg1CwIIZjKkgt+nloQHbGIqFtbUAr0AKKCtBKYWJrhc3Z2UIjBRyf4eQhiK1JueQCnqSlEgOX2XX/7JwDu7pLUNTPTbK6ugodtEMyzYOwIKQ0EgMnowZc2416+9CzAHH6a8+BWAi+Y56GnGjHQAqCNVxxawfX1y4o0Rl8YkUZLtIB+WLxa+cpAZksIU2EaQc3/chWmJYcIC0j4QRPVs6BN4zON+dDv8JkurZ2NY3suMG739mJqAgCyP4IPUELj3LrOD7HdrtfL3Yd/11uthw/9Xrp+hejU/hm72jOroTIN1WlAMAUgIsDS/wciQIgKl47JUhr7hcmH1zfwY0ZMP0qLqQVBMzLj44Bg9VlfpyO+HIRuXXFqAc2JXhbzWUZUrbNucZ5/jN6QV+SkGoxIWDaIJP0XH//hVi4VEWBpEkJXLM0wAtzbE+SU1MgFVy2lQfm30Xj48ODibG3p68HB27fP3x1O//qaYrR/BCDBR6Jrswm5c0AwVYXGvszS/wkCgXSEyrfhwAUU9cp3fqP1S0vP0RxxT4hvUwBe/Q4/T0CwVCNMIAhwpA8brBsi+Wov6VAGoaTH5YJj/m3rUghAws9LEQGC0RVvbAhMExPIdP0Yoq+A4XvNzQmA8/NjfQ5m4Tod2CWQrjiqtLKC0jQSFOpU49RqvCYmarWJiZ0dkGbx8+3tgwPw/wx+uf0T/AjBmRmsmYBUZUxDjo5KjUKIzS0txW0AgiCsn+Dn7V+ZesCR9HLpxRdbSslH2QoKhoBkuUjzHoClsPFycVUzzCMj3INevWfMa23G/RNKW7QEwCygBjEFQV9wHRvTJAjKKaWhRMEPEWAKQIAWrzWRHYAIAOQQVKnc88MPt28TfIAdjt3iO74C2duLi2/fImcGOUv27/FjAyCgt7xM+DEexJhSbMUdHpZy4G++OTxstVIpdrHDRUW9c0cC5aIe2IrBPAIUHlL4lVOPakvICy7brliyvnCHedYyyKbDqq3ntnvbS7am90ug0n47yzCoAXoLyN4G5j16vXa71/NOstsVPaHb9fSCHIKxOWdpCx7b6/lSDg6BhQL1zAwFjHZ3ARhNxM3O9npzc3iUB5++poBeWAARq9r+AYA2b4LCDBTzZQHPzzFJUqZhcTYGWmA2Tm+jCpGGgC6wp9/7Qcscfl7JL8KP3CXW/gazhLyF3dQVlr7KkaaGtxp44rhU77rMW9oxyJXl81rEeQT4+ecrK1xZX68j5FZWHNXxjQeTgw/nyZN/JgcRIO7d2zNVGR0QWL/91iTJtUxGRZReb2cntXyCX4RgrQaujS/AgClt9g8WD5eNOzE63N09OjIb+ObNzz9XR4B894CfHdo9ryFmVhAkLFnBSL0SBEvGyPsqwWrQk0rXW/j2/pO3/xjWAkpHs2rZcRrc2q3pc6ZbKABalmBYgLZ6HpSZrfvg+yCa/bUkhX2QkgtWviwA3rhBaOblme3Fzz6TiFGs43GrJVx6yf6ZC/Znexsd42j/7t6dmnrwQPCT/aOaFx5zfs5u8NFRmSyLZmA1DzrlARoNyzaFeJW/lPsS3W9qBXExyx3EIZe3J5glfJc9KJtN05D+7tfGyPtt/E0hGANdtejUBbGVDNKCWVuTlgqIl5F45GfiANZu97Y7e3sEGTapdy+OfTc/bzTXGBuyQD0ycvOmjbCn7TQInV+7ZgA0m2fQyyF4cLC8/OuvBkAIxnU6mB0hBJeXudvOA5BAPTwkGeGvv8oR4Oxsq1XKf/kXEhHLF2LUBzYI5juTyvDzEKQb5oWyzLAANAi+V8PNKVOpBcQDSy/iM9tqC+grTVoKqn9nWkqjSTgvRqkNmBiQtCFL/qlp+STTduMGs09dgBksIOc/LKkxIiqSE09dNQBC3mNtLUZeKijX662WjwBT+xcBuLh4cADNBTXgdneXlk5O/v771q3nzw2CKQA5Y3d4CABWRYCQG66eA/HwsyQkZUEzErSdSaUcuNSKs+idMEK+Oyz8PARH1EjznGhvAfELqrb+DmIBcwgyN/a1QRtDQgpi6xgIwP19MX+h7yfVA8V/djY2rDWXE1G9ZjwhCABubKTJCTskiABjF1j9DB8BxiyYFjDav1pteRkQkgMGD3B6+vVrrOvCZDGSkByArBoeHb15U5YGRiDQfxDJkhC6X9o/6wbHTLi05SO3fxGCzBJYdDZuzODwK6xp0Lacy9esmxM2OaEIO2bAdhuHm+Mb9WrQ1KLDYuooR644DFuADEC+4q+tQF4jJrbnNA0nCOI+rryJZ3ER+5cWFkpdYOSyMzNPn9ZqZfuXR4Hb26urd+/6AnSz+eef99+fkxNwaXZ3mYwIgMfHACDF246OygPzh4f7++UCtHe/afTnSzERfqZ7UGX/LG1IIWgkFKv6XRmAUTx3sCdrktciPL4JuV8QTPEG/RtVtqVn4RGxBGMx4NSUkZew4cNbPr8Nk9p+Nrbk81xbay0nrOHMqgjwt99u3lxe9pGXjwAh1VFdgskjQKjrewbM6urp6f2Lc3qKUaPJSebEBCAsJWJEtvfu1stkWQQC3vb5qWhoIVjxxSj4kQ+jJERbjqoBqPU1OQStFwaTFPPjwVA00k/Hb3gIcqQIwEsVMj0EU5tpFtCzYL7+msWEdhv1P9tkaTovJQv48ccp2eqjj/zejGgF8fPvv0/L04wAP/lkbCxOgngAtlpnZ7kF9IlIrAFCDknwe/BgYeH33+9/ONPT2JsEeiqLMPinBouJBV7U5ipFgJgFhjBSTD7Q++Cl6I8jmCkjRhZQZZh+EWAs1rGzkS42zMszV7CAV535oN0jxYYQlNvNLaDVnBQX+t3o0QJCC9U2gHutv7iIGveqNWeWTDxCChsJgrzQzcgd8MTE6OijR7776hkt9Xq7/eRJ2f3mVcBardPBOLoAiAjw9ev74ZycQGdmcnJ29vFjRoBmAfE7y0T8ZtOghwv10Zcvwe0h/4UrzTQDIh0szwNUBlxFQygdIxmkEMyrg/8XAGqqo6SDTqF/g6BSEWmJGA1cKiK0gIwBudWN65cJQRtJN3qCBCvzCNByXbweIkvJHNECpgQFOm5GgLH7qghwdrbRKEWAJfeLHBiuHAoJ1oJDBDg9fT85f/yB12aROgKwTIc4PrYI0OI+bDrB7GAux5bzAVMywrDTv7SB/xsIuiz4v4OgF6fxSkmEYCT/eB12O1qHgj+a5cC0fwZBr2HPPi3lNvjzaM1A0GKch4wV3Vle+Gqd49z+4Xnj46gBliJAFFOWl6FRU3a/5RpgZMA0m4oAIwSRkOBxAmA1zbVepxzRhf17ZwEBvs3NxiaY4NevS/uqTEbVEGaV7MblNhCsPzrjsgMewgKKFnrVSThYwNTlCn72E2Pf0urZjKgWovg2nAcgVtALgr0eGCkUz332TPsh5+YeurOzg87x6Gi3i2jQH5RZ2LKLz7Dz3XdjY5OTeQ2QgmzPnmElRK1WjgLTMgwAqAgQHeBOx0eA/pyewsVDYctbwPK4KEpSofjyI+3f9cb1hmY/qrWZZf+qV2v1hyABh24ICaql9twQAByOhlBqzNlKd590mPWTyroWpTDvtUiEUthm/xC5YIza9PCjE97fv+fO6ipL0qk0I90zCy0pD2ZuzhgujBDBm7tzh9RO/FZIkpdqgLduHR+32zs7VRYw7wJDukgOGDW/TieNAL0VpJunyla1A0YROpVi23wJCDY2Yf84djQIET+VXRsMfkZHsO/KveEBs+ASi/8q83C0gV7Y1SDo9da9/KH9jPd++SVqgD4L1u5vJiGWhkxN/ePDwfIttueifr6VIcbG8i7w1hbGl4w/zeca74a0r6Wl3AGDkEAVAkR21RYwRoCdDhyq9KWxF7gEPYsKT04IQby3agDeu9fpAHqkINAC4t28s4DXGw1ZvxIEY/x3NftnFpDwY2d4uD5IAGDOUx3WDhqfRQ44btQxkPm8yy8AMAgqC7YY0EPQHDC4xviYcEEZj6yZfAMmI8C807G9/fSpSPtWFTTmNb5fXU1HgAhB2FtfAyw14tIaoCJAOOCqCBAQ5EF/BK64XwqCpmSkoCIJQcrR2GTDTT2PKgfMT4LEueEVYJiIwPkSfFd1wO8AmGu8DQNClSfjik86WwOj7Jwgij/DL7/w8vCzYUxawLgPBJd6w9z/i8zWnHC0gIAWIsC80Sb3CwaNF/ZgxdCvsomWZ2Xlp5/6OeAIwdVViFd6DmCnUwYgLKBB8D+kXX9rFFYWlVgAwQgBtwJCi6uVQrGdgjFgjWkSAsxoLNYUCwiKYo2UBQoCKyAJImxpwP/2+67H07Pn3vfum4z6YEYTFZPMmfvrnXsO/NC57DlW2rp6lQAEE5BfvVcwx62HY6BT8MdFQLYg49i3KPzeA7AWXRVjZd7oJRK54qWaB5y6YkOLEVsOGZrYJCUC0FdxvTGN7oapNoWI1CdgJ+G3b/sEfO2ad0U0opamAj6aTkd2gOfOzWaYHY4ScF8Brq6iAvQO8O7uqAIU/L7++uAA//84AuJtR/iJBWgeZEs5qI9oCPJ7+zgAqg35ZABmBWDbaY7joOUZcgKP978mPNqRRw2JUm/UjTP88MAVUg3AeDH15Ze3b3PA3P49fVxVgJBqGwt1QCuLJq4ijIKvgl0NrAyhAoQd4iIjGAyhXQFyBPP6dT8DjPAjBI+Ooo9JpdvP748QjCowi8Avb4REpuYIgDlL5ij4afB7B8Do42qZVdnRxSUid7zaCKklGDx6UQp2lafKT0YlKooFPyZgV4EtsJaWYnUG8aA8C8xewidP9kT8+/exjI7p4GZxCGfJwJH8xVsTgpaErwsXFmlCMILxHTArQNEQxgmYEPzrL/s49QCksWKWZm8d4eYD0Izo3AuPt3i5TI6H/9aH8wBLANKABNHLAMrOEHnHt+JQx1XjPIiWJqYdZ2vvCEHP8FMSjjBcWbl5E6uL3FaDO5CpR37oSFW6rwDRnIwAuL8vkqjiH89k8uzZ27dVBVjdA1+4AB7gpUuvXhmAOzvHtSA4W1sga0EuaQRAuB638MPj9Om9q/PrvzyIyWvpLQSj3O7PP/Nmq4fgaASzMAAj3Prfyf86fmG1EFdW/ZAepmu7fPhOtWkKbz8APJ6TzalNWkUtcAzM8S9fzumiDZGshybOV1+5ArSjuej0Fy/OZiDwj3rgNgF7Bji/Aszxb2sLAPzuu8PDOgZCFmRpqY6AtSPbaBRju8L2PlgecJUDZgvBthH50AnyCdswRWecaM/kL22+1EIU37IecHQLsz2KPiZREg8CD+Pn/ii2tbM+bf97hqdtMD6qe47PPkPf++zZP4vzyy+ff/7okVqQrOiCm9rlZe4AV+BrU/D9+9gpUQvCmrKqANv0SwBubR0dUbW1BeD58zClyYP3qAOTBzBZkAgD6riW1Jom0BPE0Mv69v95dwTFGJQ+NvaFCDjvkFxlj4gq9YqGYIfZHPeUWMnSsEwi4CfbFMLv+nVAMMMww62PgfAqsrMlznRqUrrBSZ1Qdrr9lhzS85kzKyuVKQ3HIliJihVgO35pK0BsfuQh9PEVIOH3/PnW1uHhzk4dAVEB9qZcYMH49td5pX3jezOujYha1GydL/Ph3xnXgh8ZAedDMF/Z9K1HTLp9jYdvGrEOEMOvlkyUaESE4DgSVikYB7et+ezuUpoo15GmYQFIPQCxirSycvdu/5LzHmR7O+7C9VyYnoaQb4HrIXQVAbe2nj9/+RKywdTW6ivAHn7qgu0Dxwyjt7yPwZiH1Y6FDiOtvTQjIROxkfApSfj/Tci8CMgkHCHoZ8Q/fslV7DME47tRD787JSFBYOpH1sKwguCdOxAQyhK52J4jBE1NNw8aNjZVBbi5ubzMe5YagNUMcLSMxAowDqGx+dFXgDX8trYODmgOIUPZqIkvo8ZIRHUX7EbOb2rmFP407RjHgJCVs0xUFfx6CDIRs2Xt4VdvAR87hkFQzXZzFfzGZp2iFXiyV3W58cGhi77xOL1y8rCy8RiEs1kLGMQI8aAVAb0JgsePP1YAhJvSxkYtMIlLv4cP8y1wjH31LXCmIdQzwL4FQQI+OkL8jPDT89qaOJEaQXMGGEfRfBPjbQxfkD6X8LO2L8zaMbydGtsMIg3LujWmYKnGZPABfvN4Vic8fBGnWc2EreoyBPND6TcatnvuFx1y2m+If8JJoYhbkReTZSoNwgzA7e3evJ72C30EFATHFeDubgVA3j4gcY874H4GSC1UUOxRAU4mfQVIQPbpFwBcW4uW2gLiuXNYRm9bECVgW7KST5TBBzrHrVs9GOkdoq05tyeOfo8f29DBdWBsRH76SYuWBqAWLy1kfswg2q6H8T4kuiX2D7YfYsAYiq3VZ3+iGw8vxEXOJwxN0HckrCC4u9sCZmcHwpTUCTQEpZwACFYVIDkyV66MIuD+PjZI5s0ADUHOAF0BPn0KALYVIGNfBiAaEJzXh6wAWwjCOKJqQZyClTMU5fQzA/Ru3YpModrAK0Y6QhCfs61NjoACIDQSIv2KQJR6fpR2G0ZAXb/1gJz3yIburb1xhHO1tt7vEWs9qVfKj9NBw+/s2QcP+i5Rd72xBXEUXF6eVwGODGbqW+CoiBAj4Nra6moEIFqQ+ha4rgAhx5HFf6VNDSJqK8WmLtglC39ahh9oHLduOQJmGAqCiIM52SL6XX5/Hl+OeauFIOj4TroEY9QUtKRHeRc8Ap0A5JiY/7Si33sbpLI4rtbXWy0Zwk8AjGYNkabFM522kAFUJM3busOR81LPAEcVIF968E/6CtAEhPYWBO7DuQd++XJ++xET8J9/gkXTgo+70a0SqtUAz57lDrDeqoIfWESIfoAfOUU8Gt3bQ84x0Feljx9zinH6NNPwaBhD+QJVga3oqdUFByk423LWH/W1Xx7ftNZ0vk1uox//vbgYSr9azxQEIz/GIMxd8aNH/bYECFr37k3Soaja7dt4oawrGM+ZM9evVxWgDVHr+FfJsbECjGqAk8nh4aIDGMwAXQFGCKICrMQoDcF+dEUiL+H3/ff8FQefRWRsBYyyhxyeObO4/DjW7nrFMYyx3qOqvsgUiEL0UlYbpODKGbY1JG6N6HKrkY3aFaq9ru46j+k22gKYR2O6KtSiI0lBAxrN99CC4GWOdtG7u0i/Fy9iMIOLNB9Yr+Lf/fBDdUMCWsPq6igB7+zAEmIREpYrwDiG7luQqgIUBAFAgy6e2azSg9agvR1ZCWwRdnioHQH8DEE7aWY+zfIyIZh7YWlrxXlgqzZOGBqCCzYh82zZoz17P6yMzJbsQ2FZIv5K8oOIQPbo9g5J7podAXGXYabM3h7W1qfhgOvC+1xdpWlKCO7Myoov61RFUldgZYU6XBUAf/utlSNqSVgRhJubqAClhyUA1qtI7RUc4h9mgKhse/hdvDhfkpwwFMgEN8Hviy+ePMmfY3I2BLXIniGI67s2LroStKRRJW2eIVj1wU3dN+/EPpnoHw2ePXzmF+y7FPMuXF9G4mo7AKiv8qJ2tFaVVM+g1usTMz01auoqifijCpAAhBzROAL2gpTffosIqCkgKsDcgsyrAI+OQOSv4l9fAcblfO/QMPYBcH0M7CHoOjC7aQJ6hqBvkfNeCXNcz6qOmgmGX9kFLwY/QTAaskeyQQ7Tvu3Al+2+qRUr8t5wD2Yt1gh+hqBHKxWUcDlXwWhtTZr7/b/CiMZc696Rt90EaW9AMg0BNKyoB7O+nivAPv3mChD30RUAW0HKSiGHQEO1h+cnT/BA5IvwUy1o8OVWpPWTIwT7COhEjJmHCyqNXHp3uU+KgKJbqd3Ijbog1166ecbuKtEn+2j3tye26xIE592KCIK1+znlLc2bMc2BBXwtAkTozt8FblsQJuAYASsaQs+BAfxQAcYZYDxZkNItCFMwGw7CTs+EniGYox/Tb5RxE/yymGW9V2d+e8so9NTPxmwj98ETutVbBH6GoNoPkw3wheNZoMuQjDD04bvJBP02nRN+muznWeCYI1jvdJw/P53++qsZMxt/n9kMz3CUGyVgvPDXrtXNRyVIOZl8840kyXEPgilgrgAV/TILhvHv4OD162wApoMaNsIP9aDNqRX9GN0AOS7015EPLUg1C+QoRvCzqWHNJeQ2TyvwkQfP8okZmV+ecH22CASdNg0XAi/zLQw/gIi8v+zVo2dHwarxEE+woid4ihUBOKoAQeOczdSceNWcK5Db2w8fYlij7Y/9fbmDAKx7exakPG4V88KF9XXQI6Il18uX7S3wiISQZ4B2mqNBbLTjwq83bliQUvM9woyJl5FPkBP82HqM4BeJItU9cFytiGIDpuxlVX0Bb3gXXEfAkc9hjIAaVCr+RYZFjHuEoLloSsV+L8UkHKd/JHFV9NSaJcPfVxXgqVNra0tLoyrv1Knbt7MjnUbXe3v0EsmbIGMaKipA8KBtSoMpYFUBtiR8V4CTSb5+0+EyOgHI6MfNFR6pSCgJA26MgLkjNrOyrfwkZKlXrk+6vusHAngBqw3wiJ1o6mDNySEhVf1tvZzXx8AcAdGi81QRUN9GVisR3NqduBz9yOZYBH6Oh3iAxlRVgEtLT5/W8Lt06c6d7W2PrDG05jMEI7e3p9M3b/77/vzxh91E+upPFSBtuTyGPq4CzC0IFFErCG5sqOZ7h75/w2YWENRCAq/b1P06CrYQbIfPpmcxbFTwU7rVa8bIl8UHosnDPPLBAnvBNeleSypxtTxHQEKQv89dcF9F5P2sduzCrksRUIy29ma3/ZgwnE7rXdrZ7OrVes536hRMn2s9VKZnjLshGcS+9vf3B3DkYlNOwHfvQtoyA7CqAGsWDG6B+TZpIXjp0nSKaSWtFf9xg0cXjIqAGr7E7lcQVNvlpFuBD7/L3Bdrqfpw7TZKrWSXJafehQE4bwl5XhJWglWdx/vEMfzGB9owmVGtKlAwdDqm8jvvRM6exXBaf4JpXj6qAKOmQj77+z1sXSfOZvT5iMdQZFRUNAQAcQsTAbi+zhmgyFf1GhI4MOQBYvG0F8e8csWCdEy/AqAioMYwrgPVfsSeN8c+KajWkS+6ieR4N5Jdjk6ofP4gbZjjIOg+WPcg4a7wMleL+r63GlL3+1uxsLVOFgCtH5R2Rq5fJ3MjH8XDhw9hKxgPFjk3NpaWbt4cARBib6M/wy4cutoIaVzyAWCvXr148eJdn0sYwn1ucxMsmOgLhxaklSCqGxBVgG0Pzxh47150Q7/xLwEw7gSqBvTtRxy8xOqvjX3ueh39RNDPHCcd6Zxln3WDz2dBdazaL6mCYN749SBGB99Ke584f0VQYhGtQoxBJ5KRiftRhDFDMC4y2RFkaQnTtVrqBx3wCICTyWw2St1YVQLM0D1PJnfvwh3zyhXFPwGQLUiMf1UDEivAehRk+MHHzg93wR7EMPoJhKwEHQH5MxX1QNOKOHRRgyieZ3TVzLzOCD85Dy4Ov3cAbGfWIxi6DvT6ZVS0cgGrb6WaIvXw0y0I2C8t/DT9I1ky7tRJgicypgnByIKO9oV37lR+Q7yi29urGhcejGNGALRz+atXUP7DSjuUBbnGyTH0mzeqAMcQjBVgy29kBOSaQYZgTsGqAdn9EnIeP1Pis42AnlfYwCGn3zbuibMZH62gVYTgAjWg7Vql81tB0CtIakNEveoh2KbWPHqutgwyjSHyXsTTzSfvuioCiqoQ4WfvuH53ROfevbpx4Yu/sdEnxfpvwpQV4pkxAj54sLqKCtDgq+EnHiCqzdEUs4IfJ4H4nBNwbj7i6NkRUO4hbe0X2w9fs9lqzdwmwq/XU/sw+P0NwOheOLJvjfch+Takh2C/6tcSDPr3nGd/TL32+c7L1f/j7epb46y34LZwKVSDtmqliii0CGCuWNgiGJMCQSDrJrRNgAQCCYK0MbQIFEDgkv5niQoFxM97Ox3nzjm/l2efTbk+kGpiEqM7mfM2Z44fiVbJgoKhChVoZuKyTr07MiYDvH0bGWAPnjUI6WzqLuDhoZrQQyWIZQj1UqjWDCL82AE0/2UGdPtZH8uqF+fUCr91rMr85wWM4cPksQAZvZYprA7DL+eAcR7sdozgU9vgZPYjmPh53pHL+3D8eP5fcnDAQiU/sc8Y72NStuXb6f0McDq9WAbYztXYvFEJcnrqDLAewMUKmBlgr1M5n0vfrRY54MflK4VgMyAr37JPWvb9PDgV8/0QGjAeseVrwsPwW95fd+JRyVgIWv2cGZAQzIfh604fMsQIsbwanT3sMtzqLITCVVr7xg268ljr5cvTaT8DbIsXlAHO52MCcBSvRgZ0E7qlgIn8d3LSzgA1x/bNE8EPbzTntBJQyj+2XVrrmIou7lhQ7QzoeSMke2ctA77l+C8AMAfhngGRdMvZO2RoZB3nHHklPWtkVNwDUu09uvq3UCcOwYO4M+yJSwnFfga4vX101IfYbAZx/HIMqMPWWMnc3Hzy5Oef1Qcsn1wBD2eASidsre6NF1fB4sEIOT0at8XaVykTGzC5BTNmr6cW3o/P/hIAGYRjIO7lgH0DorKCqq0na11MD2oCG/4adWawAsaBxPv342kwgvDgYHU1AlBnafZfPf0e4PFxv0GN6UOfHRcBECF4e3s2+/zzra3ffx8uQJgBrq+3fxW++w4iMvO5QjHdYXlXvpYYqNXMlgtb95K1RQiS+X74oXXEoS4zVI624LdYejAAwJoF6yq4dE6qrWsi+HoeCRLq1xaxsZ9e3uEE+PjwpyMEfWtO+SCYkEBkYQIYvv02JJ6xmRyDW1u8wJvk1M9cPAfEaa7NTdy5Aw+a98x+UgEOZ4Dc8xP8BDzdxnQXMC4Yie8cC0qZnEvGsgU9/oZSufexNANyeVio7QXhUpKaRVR+03J6nBlS84ynvM6de+gxiY0nED/77F+NB5938yZg6nvrly6trYEHY20MJlxZ2dricRvIqzgpgcHl7u7m5v5+n+N2d+fz8QHYDBg34ngdbjb7/vuffjo7i8IrP8oA291IrCLB2cs5rQJvngMzBJcnWp1r+70IxLpf6wbMWO/onLwt04R5PQmR5W6fAfPmWjThMASjl0xvfNMi9UjaGV7oq7O7PvT44nqrLlY41u0R+0nLsG2I4+7dw3ba8iUI7x0JgBCkbm/fu4dfgxcvMvQASAbgszOYGbWHgZr/RAhaBWM1dH2iui0qlXdW65/KMCUu1S4e1dYQXIIBKZ0BDLFcbDBEDowMGANwNjFqm3GwfVlODKEaa/+ghmA5VWzzYA7DCsTqH+rRuM5rSbwj0u8PYvrQn5C0+c8MKDk+vQGxF7exsbU1m7182eI/ZICnp+3vCyVjDT83oF16GIAyahu6mNT3Ts22pOO880VZy0JwopXi/CV+gVstaDWX3SnXYkq0MdLd9LxrnGeFPfgt84gDCcGrV1dX0ZhRIM49Qgzr8iGbPsetr/dr53FNmAhAKAzBg48evXx5dhbhx/fOz3sA3Nz0DNzdQCuh4y4cIcgmc95kK9tcffiV65ZD+oAeBJcAYE82YwYsW9C1e2BOV/vyfmplF/1oywLw+vUchg1B5IMAogAY+Y/rS8MZYFvcP4YBWwDkfjCs1SMEWYKcnDx79p9bvQwwq38IP+2CRB2MGFAZYAmvqMVsw0/hdwz8hoLx+LOXkx4EIvziOlJpxxGpetHhu+vXF/1gY0Juqbe4eZOFCCDohgwKEvyp5gxfuizgv3w5T4Ez381m/fq4z4C0NW8DkBfTt7c3Np4/BwRPTjQDefECZ63bGaDFFiX/eTM6Llm2r6RrGNqeymfp6bAr+LhccPQsOL74ugMSy5CWE1Y2YKt5rk3N48Y0Q9Br/VUMiDc1pjFI0rO2xozQgi0zIAAI59LtbS4hHR9LS4j3rl2bz7/+GitGWBO/SBcwAhAWbTxH/cUXOIDzyy+EILkQGWD738EM0ENFwU934yXFt97PNbDzv7iFqMIxhuS2+ODKlYsy4BIhWNeC9aaQXIbfusYt3aNrc4bW78Vi8On7lEDL9XlkwDII5wcQNADj/pwa1Xzjy6fZqlq9AClWN+fzx4/v3u0N9MomjPkPknzBT/fQv/zy7t0HDwRBMOD5ea/cOT4uGVAB2OcZ1QNkH1D2GpEBM/zqAYJd/5YtPnqv9Nhm9ERWWryCDejx73L4jQuZseJd3CmKe/FDPxI+D8Y2re+YD4PFDrx8l/h1KETi5FjhWADMARjwAvBw4FQX5wg6XUjS6YOVFX4dXGdms42NH39sNUxiCeIuIBjQ8NM99Fu3Dg9PT8/PlQGen7cD8Icf3r+Pn+GTT+SDKvjlM44yYXMTpjTT8BJsCcGY+8X1tCtXLs6A42chk/bkt6x+4/0k89+4HzZDUF0//5B6v7UIakN0FDCckJgh+R25BBinw2r+uC3jA4gxA9SgTsk9QQkARiEXAApTI01bP/hgZ+foaD7HAnq+q96qgQHAf//9AH66h45eoSB4dpa/U+4BAn44qU34iQG1il7arHFloVx5iDYAeRXWXld6Pen596YBeDQAexro2pCIPyB/UP2mlFeUzFkO6qx9exqbut1jI7fW6NsLz/paBWCFYGtmomKwvMDp2UKskT3od3ievnrMOAzP0yk/b2sL52jiaE9TEANQEDT/UTXIzz0/RwbYC+3r6wq+vHBcdv8Iwax4kY6y5WdVzunjmRraTfZe0f9bDtgWH+TLmbU9Wz7qWjOeVpMJFkGw5Dj/yKV5b2t6EjftZf3A1o5lC/IdlNmlnabtrso3TlcxpltZIQfiY562OjvMDEgICIAM1cfHVk1HU47MgIAfAah76LyN/ttvz5/XxyEkByP8YMBrCDL/MwPG4OshXCxBMuTKt2w6/k/C7xUA6WhZbgBnT8Ah+6LMe8rXoj8wIFIud8Y15nhpeEiGpS4imjmqe819Bl+WKKAjKHlWlGgqA3SbGiEY72cA7uyYAQlAQHdnh44JFolibKcrczzQZQbEc3hI/iMAKY3gWtOff/71VzsDxDAw9gCjc4O7f1EF4ztU5ZLREPyY0b8p96l7orna0gwYhTa1I2qvyVIrIvRjyJ6aoMztbJ6FGGK99uxYuV6pC6T1ZV6RoWBVExEIML3OTv7LgzrynwDI4Iv3wYAOwQQA/omawgbhbAZnP/LgrVvPnkUA1vynyx/43PY8Wj1AD+EiBM2Ahl82FxqCX7yXedHOX/3Zuqm6pBqmXkCP/b9ethfzOrBSDcHWQVe5Q49/CMEMRGuio0panxubMlevsg0DYGnNE0znrToAjPxIUCozRHje38fn7eyYAQnenR0ANJug88+tLTIheNAcyPxPAMzX0PGZ7QD81VeR/1CGGH7+iaLDqc911VvXrcD7Zq2X1mfjtV9SD2gG7HtC570nkqxLC+d68a0MvGRS6WkW6WT6vCiotSBoCVeEoBsxqiklUdKfVMq4IJGGBjUyOTEzIEBZ6pJdvMzntNj99FNBsC5AxrS2NzYoImUOyAIJMKQ41Q74tc143hxswY/7vs7+FgVgNOfcoFvEgEupYVo5YMmA+vEAKn17DezaEKybKoBIfQaxt3kQPaMRKiTWlx1Ye1sVICb4okqQeaAtLgEwyRUMTn5cAAT8plNnj5o5sFJW86ZmQELw6IjB+OOPeS24F4CHn0eP9vbaOy5qF0UNNOFHvXPMANsBWFft4zChX4C04Odd8VYfcOzRwonu2dR8Vc533V7J36IFwbqWbgkZSgF+CT4evI6XbWPrwL5MMQADeJKzZq20d0UEv9XVGJ4j8zk35J+5CLl2TYL/NgOygJnN6HOFUFwXIIsBePs2Ms2WDYmf2uXKu9Pt/RxZoPhCcC4uhxiw7xlUpmXs7S4G4atXitNf1qxtCJa2M/U3UeTPOyV2lW4fhBV06tM14r7+KnvcklP9GzNAC/rdDazPIpYe/JavxsUmAJAv8507qoJZpJSrkvw7sBbeUKrs7tLXQPxHAI7jv8NDpgtsQxNw+t5xFd8aQPpHlOYAPQZsRZ6x8BO1XLlSFi+OibA4iIOHWnYMwppYiOCiYQh+bQ2foNkKwOKneJm4veXmpad6n8Q9rdbmXNQe1mCO/oN6ccB9pbeCpOullnp/33sXnBYLfrEb6Okx8kOBcz5nKBb/jQfg7u6NG0+fUkLGLmD74V24uPFWMmD0ofUZIcKvfhUWQ/Bv+P1RVwjq+Gq8myXFUWsgpEyiDGAIggrAPREBa5/yTk7rCM3QvqkONtSmlfrfSOi1zyDmNowBCMhmIGuXODOgV+Vljy4IcvPszh1e28wMaPihRIm+qvzo1hbsz+kYM74AQQ8QsHr6FFcBCGxx394eqnPZN9k/Wztvi5owzKt7r8E4AP7xGn448otTNf0eiXrDH33kllw8ZjMplShD8OsDkJmk4VeKWcsjN5EBOcMwT2bmsz1seeIhXlWKKbVmIj79demSbi7pAf8ZhDUDqpUhMCLQxUZ06xYdr/cSgDE4v//+zg511zS8HMd/cGwQ/Mx2gmA8TB1NnMSAuQhpQZAp0KJF8zb8yH18PQXBoRImDiWqQD4Gfh6a9QpsjWDKMoTVNIKjQqT7gPzPz1CKBpVyzhrqEapQUWO1tBCLDAhrD1lh+gyY29SCHGtgdwoJUJrgkv1capSNGF0wl28L7SRRwOzuqu08DoAPHhB+8Qqm4WcTk3hBACahNjcZZsDesn8LhI3w++qVxOyY8AMYCcLJUn6TE++cuRIegl+/y03goQgp5ax21/e1pPJUTbwbomCbGa09qmOh4hG7vybypCBqyBGQ5llawclrUJdJ7GqNj1JJAwC6Lo36FImkXJDIvU93PATBcQH48WOY6AKCLkGYXaI9ZJbW5i8LEP0iDVfBvc3fPgsKgp6MAXpqYz98SBCOKWdKx/FJbCqX47hSlde7duMyxGCut0l8m123kbTehBPxtKfkxwWkrDgsfekELMCVkFWDwb/h3Egm3Ay4Gn4e4pezBHYLWW1GDU0dhAk/Finf/u8hA/Ktv4HXygB14zg2YqZ7BJ8TBf3y2PWgFCKA+etGTIwULfuhNnwUdsV+UZ6Xx6tD3RRh4uHDd9+dID2M8bn/myCZQU9OKmsPrbiXikJPQrIgyAa9Bs7QbeF81tBBxcAzqxLW5R2m+B7DL5sYDnCG38EB8kW8tN98YwB6RmsIPnnCu+x2MMXz2lL8NfwAprEQRAao8ZpzwL09N8hjtsrQywzQk5AyBLeqYHdQWw5YLf7SfpDh55EeQDkkXHHd/NZb+PrXu8eCVjaijELQeHK4zYBRBSuTjwzAfGfYgdMhQqy36Ly1f2/FgGrMxLBLeOq0QLmQKNaMMgWvcos71tb0PRiEb9x45x2BNHrPuOBgEK4ZUBAEOPsuNbkHqO5ewYBTBWB7Pwh+8rsqM0Da2kUI+rpH7CCMYUF1dg3BckPSqxpxRTcqCghUvU7dowwtuQ0gWDJg3NjgWjsb26Wq2r5aucEcszd7wPCroX6mDtrfqb4qnKEXjdvqUsP/Rt850X1xTYhtf0lORhuboQ4wdXlSQzAyoJ4n38bbbni2txcDEHZECsBmwOmU6kRKKOynOATBcoIkCMZf1raBQC+DI/xAJYTge+/9+qstCv7L2rW0tnWt0bRY2FBH3BYH40cagzwRkOJAOYI4FQdEDzTUcXRtQwA3yagteORRPLojQ0b5z9cryyvr2/vscyzF2SA/JFmyrOX1vdeX17ryLdNxzwJOx1qaLvi153rFdyy8xGbRvMtZcW6qASj44IUDfGle0u2n5ZxiXJQSi3JkwAh0LY+gt0hocc0EAYi3jrxI0KXHPJnqU3OexPNqYDoD8BU+ZOsFce4e93z/Xit60iSMDXCuOUbzKwg6DZMOIkmPOw3W/A8cOzWFglQhgzkNGtso1NwWqDIr8r7ar5DyZmJu24a3DcFcQUEGmPBzO2rKf0qZpPKTaUImV2aI/Mr0JRmwndb2fy0TPhGCMc7FGxfDE9xqYJH18ioLvpMRZsOqDSANovtsEIIoGygGvPrCgbyNDNm1mVNd1W/fUveFqehb+H0xv/YCvc7R8EsrIeVKcJv/9G/c3xeIW5x8ViDSXkAZxzzlHwqCKUcunAnPF9DFcSIZ39iW0F7tII8t/RMQPF3RdToon1dN1IqaeonO/YlvGd3iLQOc3KxKADJyxG/kqFCPEhv719efP49GGq0MGH4nBNkfqMk6m+B8xTkB+O5d34An9hOr/sxhpOgB2ku16pVYsL3pknCQvLG7iuKW+vjZ0zjl3hdmAMGVTL2kHFhW2bKP2D4LZsLjlEdUdvEFpZZSGc5vt+PUVP510XH1rjavHIDmW3KcOAvPnP5GvDW9zXlHNzkQxjDWZhaEKJw6BgRxyIEE2OnprQFOALgRTp8q1++/owWBRtgMSPiJ+0r7lFMIdiWic585Z8O7GNA98kpBp9WrqLT/8eN/7jiFcHkxBpQxjpdyN2DbZEbmWrSFO3ZVqJhdhmCpqEe32039hJX8Fd4WNQnzWjK9Q7AoO6zTwXcoLxCC0rE/PQUEP+PvCwYRB9NAE6TdKZn37wG7PA+4vi72iz6gRk7VCdPOBEYIurYU/eWuGZw+qfp0dxY4MG76ixAsBygJANO8Tde4iRnQGUFCAezXHrzMO6zb3SrLzg+UYu+uZI0KcI74GOT89JMZ0AunVBFyP7UUZ/RYACHaFTz47m5DQdAzIqhZEIL/e7HxIm44t5ne2Cir8+/svH6N+4ABUX9xGCIIRuUvNyXEWkh7Kjgumc4HGfL6UT8HxlBVTQkAYVfrXB8Ab3xJ52dKEHQ/Q/TulHYmBKOaTFlXtcSuXeqAy0Cwu4dRYUbMLHpKWbDyfJ6jb08bc+LYsm9cLWEv8e1ba1TTDEthgQwoCDIXiAwhk9FoW+DnP/4oTcP98svp6ePHZkBXXzihwgQM4cfNBFxs645oZjRLvUSEoJMuZSMsv7ybA9sVErFgGo7IDH/8WDLGqKg80JB5F/yi7mWE4Pa24Ffy/7q6ZtOlYGv3PIZUCkKbfBpdDhJIyqMN13b8zYtm8DBKwEBEb57YkYccCBBKxR5jm8EM366ZFgNa3a8kADeZgPPYA8jSnrzAdOuyGZA9gZqLc0muLb2rBTR5M0ham+83w2VYkgMJOJhdnzL4CL9bBuyCYL66wRBMfb+0EXUR7bj7gy8V9XCHmRlQ3NaWNmpLn3c9fnw8QJCmN3ZdgyNxG80wGZBtA2ZAtmoJgBY/wmkLZM5maELloDwYkAPpLhLieZzbJAMKgOTBUktCqZmXaec8o+qqyHITcghG0mMG7ILfLQPmk7+p2GoXBHVJ5Sz7JVy/JfzSPCF/s5KPSf2YKOxGxuxP/ejxyYJ4U5ikJuio0m+JdAAQEFRSGuPsZEBcaHbZMcNsoTgQZjhVhaEkOboOdQ8noiP/xVqwG/M9nGQI+ieQjHHiX8FgKR7+uiFNRsT//XIAtK44mPe8QV3X+GUfBFlu4+QTYVgKXLoS2YvOSy3KgI6NbYrlY3ZpqrbDn+FwPN7d5df6LIiLBeEBaiVpVGeQJhc5EIyFkhlapwBALNRSjQSGlTKZSlrne4whR0SIUqsmQlBJ6HTvMvfK5/ow8gTTgCTtr2x3ZDr7mQoRLApFd8rwq774N2PAXMc5B52/M+/xEIY51MR5rgvzZ7/tiU6AXQANj/aLXQJ0wyEBB/gRgsPh7i6+5i0pC3733Q8/RF3WGCkzGlZVZH2dBpgdfF6rwGkSQpGhCAAa6yLwAAlPMmBs/soHzpXzywFoCJIFEaro52IJwIW3WMokItKacHejPvz/dGQJxlifxYld8LvFXDs90g3BHH5xqs56WKlOyF391N+CAemxlWTCopIWflfXnMV6gl+84FoxIQEHnrNPidf7+jUhKACCAdWoRSgiFo6q9piU00JZdgkCgFEMfTYjPG2ku42wajzcK2/dL8kUeUbOEGy3+hJsTpWl26n6uA+tKRC4R0tfeXJYnJhD0Ga6R925BEH1u/RB0Ew5GEwm85tTVWTB+LOXl7iFX08mBwfLQzNNg+chkBdBCC68nwt/w89nOoUP9uRJXRN6OoInoMjHp2GKuqza52QtQgFwfZ3t8whFPLpETQWt1qLWIEC6seE96S9fUgTOJ249Thc8avuJGZBq0SUIKiCJvYApBJWWKtFRWQVB3VGA3/btOT5uw1AgtIfIz2Up+y8mOJXWFfy6PDj+L8SwBL8OHeyjo1wfuqpYiOJ3GFZcFoD98CsXEBWkiP8AP3FPXX/4ABDm8DML4m3a2vIzMq1t/gMDRgkQx8IeXKLgkeEHBoTyjDhwNHrxgtdH+FkuM0/DwAgzCU0GpFg5x0cl1JH2OaaluHZ1ncmlxaaF8S9I6NER44Ug5OH9Pn1iyS5Cj34i0tg9M8BtU7ZIABGBSgDO5zTDhuBsxj/41wEwLwI6Jd09lWX1af8WdY3dHKMReLquydUAodgRB6zIe8Pcktdt1KMHyJ2d6ZZO1YjLACQDAoCPHrFF6+AggtNxsMywGdCTy1w/rfYtQdByRSrPmQHTSLhPDaOvNIu/QQo9CXJsb+d8SAgKhBrixGB7TyuCUs7ynpaJXtmcBQbEEM7+fl2niY/LSy5F4HfT6V9/LQfAPAJOh/4IRnzkVzE+ds8hALi5ORo1DYBW1+hPIQDjMQuCP2PWU5B22Q8QjAxIbcG44ejNm8NDCx3hnJ5CffDRI6Zj/v2X/OUO6jQV45hWaWjAi9k/eZY0wtEXVJOWc4HdK3AX6wwgOvROG3o5BngBCD99YguX+ml6RBDaWpd88OWMJO+NYWywTNOos5nXn59DI1kAvJ/xTcUwGZvGDsdYJ0kdgboG/9Hzq2uUxapq2Dr2AznEGtshtBzC6gv0y2Qw1SejUOLXXw8PIwMagOBA5AApuObWhTQTSCMcd+GRAVk5jpvjomYMs4LiwFI73IOFu6IcfpDpysQ0Hqe8WApPOgB4H7nVfFBzMADMUHI/Ojo+xqOzAIc3++JiPv8aAOYVGIcY4r12X4tqFvkrqiowIOGH32lzs6piIJIb4XTyRVUVNa6CWzTEyfZX9e8xEBEAf/yRopI8YEmkqdMT4Rcj4ZwBsX1eIwUxDZPuDZZqtFeEt4tuizCfq/0OP7rep/H4wwfcLih2QXAhBvz6KgUYEPOw9AJlhJsG+S4BsK6bmxMDlOn04ODysml8TdPUNTzH+ZzXDgZNM7k5JydVFYXOB4PZ7PJyMplO19aiRNHe3myG+0+nwyEBhMeEJzoanZ01nw8BiDMcNs3ZmaEIBsRFAHTaB3AnADVtLCPMtgF2yVj2t8yAmh5+eXOePYP+fQ7BUiZQRthluBIE6R9GyaJFGDCXXVZ6jdOO/EsfH/e9++MxIMhLHwR7GXD59cN5kQzhxdkZvED86jKBGMtpmutrARDKUYMBc29No5UtT55Mp/gvWluDBHjTTKeInOdz/BkuL9XOORrNZpIEqeuDA0W1T5/WtV5TXf/2m64/P4c7MBhcXEClRcsV+LUEc4dDgDUNReAHIgaOgwhuVlhZoXOP3mO0bclUCoIOSiIDMgo+PGTH4NUV9sg9uzn0AgE/5gPFgHldg3EwOTCa4fxIuNfJ6LvCEL776nyy7jMUr1xU6OM/QpAMaAiWNQaX1kFYDoBVBUghF/jgAb2H+Xxnp6oMQEXB43FVwRPb3Ly+pqYU+G48BleenLB16eBge5vFq9Ho+hqwwb34+7Kw//QpHhkrDgQOZtnOz3n9+Tnue3GBZ6Wq/ZPPh0JqcA6GQ/CgwhHWR+zXlvaaeEKPY+xiKjOgVKcVhAiE338PTqThJQPiKAhRA2t7YtnKXk5Dl87jzyea79gR062PFbO6DCmU3ZCr01/XihAkEzpB45Q1HbNOBryPCcZ/zPExoQVgTKd4UoQICE0uLhCIAIDIvgECfB5w487ObAYmRJAymeCFAIAAz2g0nQIagCJSJjDmuNd8jj9UVQFQJyd4brDl5mbT4E8Mgw8vFNdTr286XV2taxhhPCY+wwxHE5xyn7OB6YBAOizPcXjOmfCt5r5Oyb8BgGhZSH1AMCAyhTS8P/8M/gMAYxwsCJbUn9NSXA7EtElL7ImUUSrlVIafKv3kP4WidqbuyouMk2MIGoh3MuCysW/eMEoAgrFgOvnS6AGOx20AMhVyeckXhp8CUAlAeGuAHK/f3wej4jnwHYCztUU4KZOF0OfkBKE/+G8+16vD9dfX8A7x4vET+P8cjxmEbG0hIMmDEMXBaaNW5L84RecpFCmw0gRD1hfXgAEBMhrhN2/evRMAaX5z+LExwaJEaVs+B9O7OZAMqFZVeYGxLTWFoJvm0n4n850AuEhlXzwoj9AQZPXkhgG7xTju27GM/yICsKrwRtOBpQcI764NQEAI0FKSZH8fploAVKCC7+ChEeJrazDwJyerq4S5XkVVTSZVtbLyzz9//w2P09cjM1lVe3vI6wHW9DMFQIUe+pz2yaSyxPkcCmoINMMECZPTYsBXrx4+JAPGDW9mQC+foQcYIWhJkIfhxHJciftij2CU7IiTwaz+pptb/M6b9fQ9vlJhbtHmEkNQSWpD8BaAjhdTKbb7+YBiwMFgNAKA2JV3fQ0AlEww0tOqD+PA7CL+BeTAhXgksiQDDz4HDDz4FUM+5+c5K/35J8Cv17eysreH54URhgnFbfwjmwHzFEyZAfPeQ76FygiSawRAqW29egUGZBQMBkRHDATNWSlhUHJ19ezZ1VWcoksb8wE8riEUF5IByxzIGPj58zwVI4ljBiFRlEM6kH7n3e7h5jtx5aLFiZwFddbWHpRiERvg+7aKCoAwfEiN4KVhlZXgFQE4GABoR0d+UU1zdIT0C67HTyt3RwCrBgLmOz9fXQV/bm6CCyMI4fXN5574XVkBYCcTm2A2WOzupgz4f+6upqeNK4qaNKhqVKSgSFjpFBnJFptxkBfUlorGg2TZEshuh7CqhAaycKaSV9n1B3Tb/9yenJ7c+96MDSmQNHkSCRhjzPj43K9z7/Vns1o6Hp2kXmQyDY2mqrgQ7vu1XwhCoBzU7qM//iAMFQWzHAcDTIjZZAabAxiK8tfBL/QCTRcdM6BU4mZwra7FUIQMKK78eAj6Ut17BqyvaHgI7XIIQJpHBPEAECLZJgYkN9Ek6knL6A6H5LzZDMNuh0PTudD3w88zgr66WizAtrikz58TbhyQyUsOF2Aw4N+Mn5TJAUsTgB6EygE2AbDJiSYHUn0icYKCB0XEfu8cAAjljOYIWiXEi1gBLoKMsxn8scbMJgga/MSBMQPGYQhcp+a6FtNdNnTg4xSegqAkC4Ruq3n1iORL95XKK8EC2HS7P/5IKI7HzQBE0c4DUGkPABCFb/mJ3S54UQxIz/H0FMlmih8AUUTJuLgEoO999b4iHksRnxjQ5/+a2c9Pa6jPawAArfBlk6bJgNQDCoDcvMmJ0pojCBYkA1IzLeNrdV1NQxAXMhVjADTfDxGwDHATA2qccbgOzRrGzPBqCP2H4eKtuzU1+KPEtLxLwLHV3M/2MPzndS7IsyGrh1Qxw4zYBBOAkwkB6HNuTQD0DEi5Ay7IbPbqlXoscC8a3MXC93zFAFRSgQzI96pYsB5+hH9hfWAIW94t7WuelzGg9IBiQA02QiQMYBKCgh9TMAASYeXZj0wrI+yrwvpMDBhOjVEthF19sQC1+ZX383/Cyv5/P/8AMNT8PVwZjv/KBBNEYD6sK+D36wyYpmJHr3OuAxBwM2Eob6E0Cmc2Gww4eSXLXr8WA3I3EL1CJakZBVOTJgYUBJF83sx/zU2eACCNYgxAZgQ1bxoA49Ibk6xKBUNwMgjRYkXOSiCnefip8WgdBGmEfR1FRripFMeW/KaW2VD+IWtZH9f3sSdgQMSFtgvuvkGIByBSzO32aHR6miT0AJsACE6ECRb4kRTGMzEA0gdEckZqZ0a/q5WP45FsQfav0zk4INyYJCYHyisUAAkiMaD8n/XcJw9QTOAnzigIQdKDL7TfS2IABNjYmmlbN20LsE1U9QPaBC5xoBlgjMJAkoVLwq6vd3Z8KsYzoDKUAOD2dlUVhQcgr+HmYfR+nD3rIfdrMmuFk/j8tPv70quZYJA3eOrPP6FARk3ETPAPPxgAAQ3AU9w2nUKtFzIgZVO4Vc8cQQVNKvxAsVBVwRRXFX7vakX4EYLkYjRSE4CvX+NFMADepVnTZjIYh8ippwGmqfMvuOUE1Re3u+tXPgiCZMD6XATffm5xsCC4s7O1tVikKdbhdLvL5WTCCjEMtwmyyIDzeZYdHfXenzQFLdjb93bbZ67H/bPFHwDYdB6iachMMEwcQgOmlmMGhAlV7cOghXugzusBuL29XDJZowsBIE+nrdZohFqJzdSnwBRi9yQ5PVXqdXsb9WMU6WCS4QOSC5sB2HwtCD/1yrGeakGORr5JrWITVwXA/X1CMBx3zhWshJ/JqUyGwEBEHW/eDwT85vOwvxh/GQedM32jTuGiSNN4Tn+7jaYJmt/bQBW3QDwAAK3cFsLvISBoJpg8BsZBBGsA9AzIThGkUPCHMbgIfUAc8ORqpXXYsxl/5uCA4YYGZgD87XZVPX2K0GaxgBeoGBiJaZbN8HxoQg8OAFgmy837DC+y3SrJK5x5k6QS1BjjBhNse5moQua4YCmmYwAaBD0Ad3e9/2biU0W0+rDelhBY87nmXxO0eR7DVCfL4IDZ0JRNEPRbte7rqrXqv8ou9sMCEF4gjKV8BprgX3+1RDShtlqhUMb6B/N1AiChAGBSdFAU9PWOjnDxYGw7HUAR8EOPRZoKcrj9zZvnzylkABw9A5I1wayokFhAprSE6QDDBDREWFodZjP5tTjBz2Th7FXmBcllu7v1PZgwytZaGcJPS3TgzflABN+Zz9ftHkkSzFngo+ztnZ83DUOyjmTfUX17jsN6be7NgM1NPw8LQHiBVKIorUsGJADJdEij4D5HR6MRVz6DkRSEUIsG35AdJRcXoxHiZvIfDhq8kyTLRiOACbeXJfwy3KvTgcYPLwD4T1Gx5AswoQhXkgSi1XjYkZcnqQSnwZU2EF1LJyxbJ/Ud9qBo3r7fTlzfBcyww47Sx34hgzep+NjaCmEVDr5MU6z8wtnZwTX1/BiPyOTVvsur7yeI3ZsBH+/A30oSMQd0f/gjxa8ACT8XAOGB2QBvhCsEnADIaL0oyJS63OOxgFJVdjv8QnX7k/ckc53NKEfCv2RA+nEMb3CLvLuimLw/4w/HBvyC9ejbYQiP4Ef+8wxoa3ikFrRFsJIX+M0jHoK+gGYdIASg1TZs6n6SXF7meVXlObudtXedYPcjQLJsMhkO8xwyX4Ml6kl3HZv3ULHCowIQce1oZBmkxeLdO3qAyNXh5V4u0ZQO7d67d0VBveB4DLUypKH46cEAwQXzgzQQ8NdOT8lxunD+4JblErC0Gc/QxgDmWTYcCn4ARJYxRUMIQl2ISvPLl3/9xVugx+n8e/DZ06cvX9q8f87V9yvGwH8q/NtaMHqANMSmYLEKiRguXEJNH5HdJeRTX/XVdicb9dvtFoUmlB4elqUGfvR6/T6YUkrzJLm50e48OBBFQZUk5zLcLbPnfeL/NQDR7GNPEqo7yQxirwX1XSUDqmo4pMdoB3GaH4smrtP+cRxJ67vdqtJCbM03BWirqiw1CV+DeTVVn34g+1MEslYrNlLajUEoEYB+Mqhf+2X+HyD6229+b4lBL1wN6yGoR9IaRZuJrw3BuI8sRpJUFSenysyfnGgQOlIyeW7DPywu118uFoWq6K6s9jCB6iMDcN1TnM3iaAz+nrrX8H88Nw8uss2jQtJkvTutKFdrFgRC2wBiEFR9JN6zie82AdA8PgncvUDe+2eKf/khKIYAtCKd39GORwD/0Qe0+oWqvlbrffJEzsXlZTgLEI8EKRqbFL7/XkAdDBifgwGtGvLtt+RHukL3e23/ZwBsPuwTCQ88PnP8vTdHo+q/i4rKJgAWBcGES+xXXBv02JgTtufYEjDeo9WK3yYEE+AXzswnGA8PbXe5hSBa3EIIagGiQQ9fqXfEIPjzz+blWU5RqRjJDsRrvR4f2b8ZAFVexXb77EwuS54LgCEHapcnE1GfDgmPBsAmCZN/58QAg5G1SSHoWotBpW5fZPkg6rqdAQU/XuYmBgyXtsQ76OoMqHHfNLYeFtadJvVxuBZMa7fFmL650kynn69lBtgbat+Ivr8v0zmdxgPCeW8B9PJSDOd7SgRA+r+8opD6fkoq+iwMCJrnO86fwcAAOBxCSB8mF05Py1Jp5nDFATvaQgYU6OyDU/FjCMYA9EtgW634WfhgQ2EEUyO2TU5em+bE27os9c3ZrnYDnu9zUyQdiqj8NFRBkIEG9EWY4F8H4MkJOfzqim+lq6twXKXm/atCBKium4D2FQEQWUGNJ/I7wk1RUk+tIqtvY8FD+C6XIVORAWMIhuCzzyhUsP+1w7Pfjxmw3catNLlgOoMfj2axmBShaVJ9vLsT8NvaQv+cGWcbu2YqFlvIIPgdH9MD7PX8/riwX44tqbqaWeb76vzWJCTDBMCvhAE3GWFK6+P1BDZvtA5PCgjkqYUhShyw9HrwAQk6g6CtcI1NsN3y5o0HR5MJVqwLTQoVKMrLqU67txdv7I33dfT7/rf0+3om5sdpvAfZ1KSnmgVIH/DsjFdpufSTDzyT+iwh3+S+tR1hiDjQAAg10lcCwE0QZHNRCBuISgkxDOqpl4q0HKYsfRYQqehecK6uUAGxlTL6t8kDDD9CwNQZEIZOM/m4FMZEUjaLSsbZuMizIPJv4e8xPoZoy/e6eR2LZQEVBZ+fy3nxWhfrlkMgEi6CSNPYB5QXWFX8W70i/Ys3wZs50INIpSAthqmHKHifa4R2UfjiE7J+8+gwU9d8Yga01dbaICyOqEfBZBpfDtNgNGsBD7V3VrE1FowNc/jc/H5PX/HwklN8/c03SrNcXoam2kNQ97EtTH5qvgGQ7fvsQvzqgxBVSZqNLE5YtQxDi60tvVuV5YqzfOtghwOwzmbDIVLSHoIExvU1vp/n0LQcHjYxYFiNhQD0/Dz/5xTFL7+wC80X0LTJMnT9fRyM3yxTSPiRBeUFQrJflmdnZYmGTiWhMcTD1tyMx6q+eAjSQw0BiPsaH+sKqHeG4cynRcFnBGB9eT3FVDAHTaoN5PrpzYUeIlosJ9HBZfVfz2bX18+eHRxA4trpvH3b60GyqSrFixeoUJycTCbLJZQ5vd6rV5PJzk7dB6TZFSedn0+nV1eQgEIEmmXj8fU1oVCWNzeekZF9EwiLwm5n8YwwCG8HfI6P83yxuLhI09UqTS8uptP5fGcHDIi6tAcgs4axVB8fVgGRETb2NR8Q4jX64XX/b7Md+4IB2BQHQ528LsuHOJiQCaGLqi8rtvo3TXFZ8dXbt6zjQvVXFKHRh+/IqJf7LxcLDzcU9osiTsOIAVHoWizit0m7nabzOWSj0N0RyvooSy2NyTLVl5Pk4gI1YoYhdnuvV1XHx1U1GMQuQKeTZXlOBtzfNxPshQtm8r0JtitqNRPzkjUkfTT6tEmYzwhAyLPiy7taMdGybpEp1Ci4YN54w2iguy001lS6+ACnLOt+JX4We39hfE2F4/U0McQQ4dLwNnmpfMzff9/fPzuLuVMc2O/74AvxOmLiZ8+Kwq5Gp7O1dXMTg9/eGpMJm43EbtNpmLT2jaB6s2oAHZ4hq8FmgHU9oVaPS3Hr+qK/EABujoPjlxfvfPgjYerAG1vmragC1IuF9HQMQNwvvKUpsfPddz/9BK/rxYs8byrt1X8CAHzypN9vXrSqn7q5OTyMS43wvQCIovC/qd3Oc+YcPetDs7Op1JgkYEEITHX/es5Q0a6eaa9nzxlCNxn+qjK7MBrFZbjHNb+f2QSzDzi8sByoVg9PZKJRiy1LD9yjI4gGbmPAbreZseBXwv+zPR2bDyPcuvcaG8qiiBkVIgAY4TjFPp/TC/TpksWiniGIc6ZlubcnMHe72k4SMiAeWW9WvLntN/9N3tW0NnItUdl5OBDbq0A8YQAJJLyx3BgwFlhICggbZCQYRauAotZGGcCrWeUP5Ie/d15xUh/3dqudsWfGziWKB32r+3TVrapTp6BOgXGzd3dqd4siUpFfHn5fGYCpHZlOsQuscm+yt/NlustLlMz2ARBkrSq3fnRU3SkRbRssoHWW1fT2uI0AIwVWKd6Pz4cN1NrO2dluV1fppttFfCzuHOLmtvVcs4EfPvCd3r/fbPyFgx2n9T6gwz33LKtvEID2qkrrwasVdoG5JAx3csOhT61eXTWxgHVQye//qi1glX2OAY53ohKGnJ6mllECAr+vbfIJHz6cnNBSjsc6mNCmfCxbGrvN/NYBejofP6IK9WYBSNjJX/n/n3/+/ntKSPj1VxaF8g6z3/ewXa2aWMDqtVweHKTUsNhZoQBEdN3kfS8vfaUHVgogidYdtQlApdrpAh7LZcp/XK1OTngsul2q0FjxSrtZkc0GArgU3tSVePMWMO4pRFTXrr/+QhKmKv7DjumHH7wFwh4qBSAOf86CpuApitznXV1NJqmlgwtOI/Rud7EYDOI7Q3s6bi9Q07UBlDL5Npsqgi0ChrK8vp7NIkd8NDo91X0dgxxbZYH9Q+MpAShxb+6T1mtpTn+jALR2z694MIoCTBi7nU93TDZgwGFtCsDRaD4fj6O16/XSkKIo0El2eBitEmLWGK6025NJWc5mObjGNDs6NdLcoeT8qtxuUaDoJnVmum8kvRcLXHr9PgGNyNhXmCWyxyAyBeDNTdqWrhfiG7aAVRCMDqnX63R895a3LCBeWhtSFGX5229NAIgTAA2VCDe0PqWBCbJsqbVDgiVeEnd3bCDaF7mCCvXwkAYw2+3Rkd/XeheN2osoY81maEWdTh8etJ6svwdhhA6znkwE6ouF7APfv+90eF/+AikKkXx6oy44z41Bh2+EiQIC7sefsNFos7H3LJdCGtgPQJagmDtTC2bHRbOZWygG8bkILSL1VeQv8PzptK5PBW7u/HwyydHMbBgEbUMP+tVqNuv3pQINyyz0LOX06aeend3dodlyPmdVB6GHBB69HuYA6C/ByJ+YaMcAi6dSSl4RAHM/JnV/9/e253c+9ye1KHzKWKjoTQEoG/QIquiUiwJ8Z8ii2UHSAta4hd/trq/ZRHl9XW8De72jo1yNBxlCdezdbpoDQBZzsdhuHx42G5tklgROfE/LD18sUOKT36lHcr0GX0hIWDraR57/ZemoXzkPmGvPtI3SaQENOzb7CikqNbeAOHXRrUanOBpRDjIFYLSWoxHhd3tblvvS2ejAzVnG4VAvAug6VOUAul1oWW23ZanULrALq+oyj4/g/MTLYjCAMgSlKUHk0COg0lHNWJ2vHoBWs4AnQK9U2CJ/OuA6/AYeJPZmAGTr474s22AgvR0pANPIFjQAXRFeMTKez3NQgRtXCKxW++osECXB7xbJI9yOj+OFIRfrwwN4kb7edHWlDagEoa3Kf/r0LyEjVJXjrAPBDi/Whe1JhYXMAxAuKgWgyGDsAyDCirwLTuspsgPk8tSns7Po3BeLPM/R1qlBxtqfZQRotc3p4OD42LtS/F405+MRu4lhv6DCj1aQr764+JcBsKrsxh1e3elYr9HG2BSA1B7YB0Dwi0VbOQIwXQpAuOzIvYPoiP8OtKAWFO22ggdBQ1nWaVjpe5FSywZ77J5FnnK9FqKZ6iHqloVdNcfHFoAqBACG0JvoCWn6I+oKW4gPqzNkOMGkzj83AAG/1AXXARDPjwBcrfJxMQQhLTFAHWC3i0uqig0U7SksnCo7iCVESY162FI5t8dF+wo9/NAIS6ByCNArBqAKXO7/GXU7nvm836/TtFssJLJtCkBp+N4PQHHBTwNg6oJxAeXj4nY71TPVXCEE13LFwaoWBdt8bwVJ5GZj5MGgCn7QyKEv+vSp1XoujdwvDEAr2JWHnwWmPJPNMLnThCrHjz9WURPY3wDq/PMCsCoIeSoAp9O8LQOZKm8bVyuhrTbj50yn0nzlG/D9PZb8MB5jeKOd62QhSFMAUdDn0Aj/KhbQTxT3/DJ9zMIwrQdriCHphqokg5A58xYQwIwApOxP0yAEhM8YhMS4tj4Kns/zFY71+vAwF7fiFcLqQztlDM9y8TqyeWr7rAwJ/yUzkpljtYCLc4JpCqCQ9Rzap18cgCpZyDHvVmtaZ0xEgFYd6PU6UoqihURatrkLpiTkvsgWXbZVaZjoGpdLFZP87ruYB5xM2DqefkLushKKFRPNyBpWVW6VyfOf2tXp2A3M/b0IsucXc7IAIPVgn0uq+cUBSJBxjo78AJ25KY/wfg/BqjgYTD2sqg6Ri4vhUGobzS1gCsA0twedAWmvjIUztATF59r5bHHHBwJWzr6jhyOXkobNt4NtAMLpFJ13Uf2Gl6iVlbNK/bzXhiCwr62axXzDaKTTUl8JANW5EngyxETGucjgd6uz7GFZZeHYvZWrn5KO9FQLmEbB6KFLLau0l0cH2m5HxYZutywJv7L0+zq8z+1tztVCNDd3WYE1LRaw399s0KEMqhYalubz6XQwiGAGACHHOx6zZT/C0NNfVcw4TkeSXCAvfOu/XoELxhgatX1y80O//Cw6zqMVieuff863C6mSp2/jsTEwyZfNLSBaivZZNXyy7Bajm0zJCOCyEIARrkVxeHh7m7KtsXfN0xIQ/kwm0+lqNRggp9duIxGFoAJJZ/RD+yOBlvzHx3Ybg3gUgtYm+i0DOqgVcn62lGYCRR/r1QQhav0szOzg6++/j4MQBYR0yPkOMFQlhVzk+S/WoZD/+zkWsNdLLXC3O5uhpTt+L3QmR3u524lYUArXwQDZxNTSoWXp8DDXWYJuuuXSfr/HR6RaqOoQX4NWeO7uKLNmbSGdKi2zTARIwdfpQH2Wv4xTqF5JHlDDDg8/O309B0HdE6YyRTxNIoV2cBBPOolbbPX+nD1gr5ebsnF5ibFXqe06Pc2xB2ezskzhut1iH5lWcrrd6+uTk+iwhQZ2fh7ffzQCkRTw2myiNcVcZK3wao2DEGQCazzmZ1knbGcjydhvOe5kBebnx3xjAJQvyp1fOry01dI5xApHDANQV91q5Sukmw0pRzmWCXZfpCV9Th6w3X54qOfxeQCmgDo7G43SX9BulyVIrWmL+nKJb5GS80GhUF1n68oxKQBOOV4oEHOSd0cBDXUQC0FuFzCyUbuDoUAmwMP54HlQI7BcViVgvkEAyl6B1sxCDZl1haC9aTiiExdz5TgmYWDjcl1ro5FK/DR3wWke8P37sqxrM/cLSs5NqhSwTiJTpOMR9BErHWmTM7i332/2/lIJ2Wz4LtAI4wRg/F9GmLH+obS3iwsoSYgMMqef//KLXkCY41IFtZeAYOvzHbB1vwIzgI8DsBSC2GnYXaC65Fw5ju2KVYkYq4rc3ALmouCyrB51lQLw/HwfXYr2j7OQ4uW13UoHb9x7jseShG7y/nIEBGj6qzkZqtNRnRsZ1GgF73o98KZbfw/qXa00EbXb1U+J+6YAyFhWEy+0fgK/d+9oBfmYj4xp/zCgK2dB0Pcgu8CccAZj5OaE1DwZAQ3bp6d5q4NhiSkAm9ioxULFMiKgEAPjm8TLaj6XMlx1h1wsVIqrVWihA263Q9YwwhTTorz0Ep652yGGtrQIaOS/CkY0R6cykPDBh6YCrA3MQRCv7HTUXVh7QB29XCJGynAEaFMA5viAItmYT3Yvl9E5A4AnJ9ttvcVEq5ROgPMJF6nfSL03jY3lkarElD8+pFTVtbGu1zwbBwf7LetigXl8rwCAHn4x9sXsIZlGqbPEq+wfdyPxmse1qErKZZkmixkjNwcgxb/T8tf19XCYq8ekDGZJfcMNV0Ok20U0y0lwP/1EpXpPjD058TKbRWG7PaKuQjw6oiDBWShV0BKxJ131NK9Umi3S8V8iOdNqHu1G+MlOzjpgOl+AT5pecukYQlBGAkpMFuvBf/yB/BcEFAViEQjgQouW6HCIeR6xPoFBCHlKfgQgFAvEykaQYxcaYakTjaoggrYpwI87TthdGyNL/SYVakMIYmU1qnvs0BcDBR0llmLSZ3pBrNc3N2XpiVq248Zf0Dlx8ijN9hKluVaTMMPyWtA1RbqBrXkQfjD5gB+okjYStnN4xfnahCjI6nYhryWDrcQR48DZBaE2QE9KVUjk+FfjNf4+RM04uYeHF27tdoBy/38LDYzcEaH/DfcjG2gXYEOIzOfrddo1J9aP0BO3Px7rO4zHCmKMm5VVFFB30W43SFbe3EDPNe7cBoObGzpfC8H7ex9Vo8XS0rKOjwWINzcpBItitRLnWw/BlxCvbDVxtQg47M2mkSMEOe4lWkCdPs5/22yh1oY//H91OlbZGZZwYxakzFX9GRKTm7D8K8oS9HU5uaiy+tXvw16KSiq0EwaD1Qq2Q5Lg/l3E7RMmZTmdXl0RRJDzwLguL5SLNRzKq3Fjc6jcX/69OLyLazjE7/r4EZxCmRmKlnQIaAiRVPfXCsHFghNDFwvANJ0VJRBEmU/Xcjkee5qchx8BiMefnyvdqotyBWy4ScyLewR8vuJrebXv3skwaJlAZOEXb74kRH18Lurcy9w2yOjWSZCnKzePSHSRASucXC9fTqlyGS4Ii3jUcMXpHHHxfn2u3nd6xP8i/GR0jozPIXlU+9g8l89bRB1Sm4OgMqExgx52z07+rbeAAkH1ivtZ8f8YgDbFQmJVSitI4ScOWMZi4a84YSEeeCuYFsN5kP3YrM9ZmD4EwMkUIrEpFnp5HX1ve2Wfyb8Sd3OaRx6OfgZmhCgtYISrfZZsLnSUICFD2EUqaWw08pNCUysorxclGL9SC+g9Ig3TfvjJbX9Sp5WHH0EXIVgNPlkSfMhYPkbBQsHy8EtfKQdSQhg9bCkEdfRqcwjitm+MQx0kdZaIQpHvfPSPVwrLqF4vYBFoeeilFtDDLx4vC0H7fvUAzBml/d0+pKYAfsDOkwFImpSlllqHG5PONv0Cu8fRpAQgf5y3oDn75y1gnPDm5/+mB9a/qs7C5dnDT4GlTkG31jDv9PeD0ENxOOR0dbWAHoLRCftGIw+/PATxasqxNYOgbaioAyDJKZojeSIA1ebZHN8+y8crERZQ4IcFAJJb6504UzDx9QxivCtOe79iI45agHoQqkuLK7JJ6mDsb3DqsrPcB8GcvbTgw+OQ2uA2wX7bFH4xDIngawJBe1ZsS1keWmKa6iCotGQWXPdBsJV3vk+BHe2fJJ91Oq7sANlZ4C1gzvbhkHgYRJJ5Hjb2r56GFEJ+PxVPZlw2bvQdZ3WOWlJHsu+0wBLHHe+P8IRLV7UD6zA1EMlbwP8Sdza7iWNBFGYTdTTSoNHMNosOEgvWlljTb4BGIqyymHn/hxidPn1SP7futQ0kYwniGGwMfJy6VbeqrHdW49ciqCOyLypAYXJCD0PvEVhK8Sg3SmlecwhusvGN/m0fu1ze4s0vr477xx+mf/Pqpw+VSQxt/f54qcxRWyFhpkc33uNCD/nHkLUxqvFIZenocLSIGw0qbv/8w0dsLCmjy1ElnunNr8aA8T22CNqPpodfhpHvSfsTFyJo31gEy1tGq5qLRWft7JjtNQtgi16NHDNdGHAxDDX9pmuuUQEJoH5BI6S9EvmhdoWYr2r1I0kDKmqafYnEDov+Goz2f1TIWnPHI0f+DL2ZtouC2VaGlnCD+dYjWbFb1a7HgAw1L1VAM8N8//m7zw5HHJjVxWUSmpgHP4fg5s9fCyJCERFDzeADaH//rXle/6gZYF0X1/Aj3payNVLAZYvpltczIUjUorkSfrko6ts3hL257/lM50g3U8Z4pDxI8F9yO1qsDDXHjkBQAZcaHUO+LSjPCliP/0besI7Az00Iyl5Zi4FogL1pzZ+lFaDZjJf27AAosxiTCqhvdAqkdVizNAPehJ8MsC5G+tdfXv80eXcvfr6YpqdiMbwdj4nI1/n8VC76MIFhRjofLbstsTh8vTfdx6/nhMS1egQYhwm5dD1mK3ExFYzjwaiAPQQFX0TQ79kBsHU15FAQMYAXsWO0zx7XOvWPV/4BgJJdPzLowTXCjyhg7AiEcMM6bjyyVdgBMLySx1K3p4ULPsLv36GGRLGG0Zu+Jf7zEjTjCLMywS14huiS1+zFA1tDbD9Jn3bihcojyCKzNlYc9+wAGGs3iF9ELiKoJauh1z85IEvxaxchxgGCaRTfjNcsLaxD5qsZsMzEHnl34wVHO5/5mn6kmD3Q7LdHoOoGQjku2ZpIQ6yyFtFNWoZ8H0F+WqZh8UdZRYTNK7b7ugZSfRYKAHNAWYqWF/m48G4rBLFI/2iATf+WhHHiYiagLWR/umNZ3l6kVka8elbEylExI8dSofngeW4bGZ2e7HSYi2SgjgxwT2szgjYO9AAqOlIF6CJ8UQHNJA8UMPq0XuM8agqwMMTcoqkANPGDAfb6V8+c9Jf8++uB9Fj41hzTDHMeHcbIZI5rZkx1n/fJe9QRg14Iei5MFBGM1Tu+bDb++NoAXdTCXgGuZkU6CigHw0ZyfjqNuAk+bGGEr8avNsB1ueacAi7NuIi+muUuVvC9vOiea/h7OGy3/SZyfS00JeyNC1v8/GxNNQuTc/zqoEurgHx+L/7XR7BVwJ4TUqehzC3aa9ToI5jcOJqrltYEe3X0BphXnvWpV8sXKeC9vRoifIBN+DHPA+vET0CuQVFjzdqlMu3Ksy1R8SKKdUS0r4D+KMsNsB95RgR7+NUuxnIEBwCaoxFhigsNq8fP76XnyADjjVByKb9rzK9mKB+b9ijtA27b7eHg0RsjODbOCtn0QBwFnMZB9iXHiAjOK2AO+liwJ/70owG2ibjb8et/oxuvZBk/m6fEf6rz6Hu/MQIoBVznfnAoXJ+sQVLh4k2r38qFwG23QhCPYR0wLkXQtx82D9mHar5qiUHxjGB/DBhnmg3BrIA216v3G2dB1mM4BNDwi6rnAWSGs9SP2c6mf/ZM6B8B1OBzLX6creDpAQ0buRGfOJKLN2pbBBL4nU5bt+g/HJH74O/6RpweQdPCr8TPz1XX+S8jBM0Tj2GY2B3QOpnNZ0nFCvD5EeAAwJipAfwwBceYIPNcOHq04DMaAkEn8Zh8n1sU0OTaDCbupWBY41YzpTKrhpMHE/9vm0UYyhG5HUFFITmL8v8oYOsDj/DLCQ9WPGHfXNvRO85reAx9DyD7b34EGAD05ldIASpixSm5mAMDBfT4yQArC3o8/dY3wIoYSfEACBGinsmlkHHlzfTRHqvAy4ugvbUlcUTwK1SwnZnOLsjS5DFzRWL1Dt9Xi6APSfeiu1UftIUAMswiAP/99/ffcYFT4VdlABqAXJikYL+UW/RPBtgrnhCUutlfoXg6PT+fThHJZQhiL/nHt3TE1kwPEMzzyJ81NmwTI+rsl3lPOCYmWDJCbjBvxjh/t9X3uxS/Dy84mmAqmsevl4JqBjjr35Lpt9bf893Z/SgtIqOxoS3ESF4ujKt/bIyf6eqtTdmjFmLyDzPSGs1qTvmxKGYE25yXOfh0LSUh6CMQvfZsVWZML5BGKZnrtr8xrzb7s8SPaQX+0NaALXvN1MnYL2GsfxlB765LAWuzKbUz/Lhdf/1/40WvdM91ATQb7c2xbrrH+3ukqxLdkLVh6OiIxFGgZTH1r4PgDXEPvyUXe9gomqdk0mhSlVif200qBRUm2Kboov7N5VRXQVZ763IN+ghGY2xOxboFptsU9b6QtwUrLDWCPymmMshIP1YF21SEJWHonH9jRlhXN5gf+fbH+JqeUyXxAECffhANKvGLv4yYM+jdF6Ham5iuKkBG+mfebR8/790udTl6Kmge9PKYYGWGDcHoBTJQI4P8eATXKGDOvPZG2IrIet0yqisi+LGgT1OYn1D4qGXL8TyO6HyHP5uMsRoQn7ZA94P6N19DrKn0PoAa0Y0U0P9/O4KME3pv2scTl85H1xk7bEiMop/HuyU5P3vtODAXP/mELPnBo0B8PwlBtMzPZ32EU/J8BvDzrTU8Vpa+YBDyuf3csAq/KgHB1+Uz/ldj9UgA/TH8vLHNGt+TScME188MyOTZ4CXZMBWC2dLNNabvZcj4epEFADIJK89nCD8/NWMKyJigz3Oj+fV1AXafSzGFX25eFE/Ye789BDM+2wcsOk5vcm8dhFTAzwzGtMHoXEM9KgioakRGjogf+1rvjFyItDwB7sOdyPO5aq5mJ4LOSL5gyVfDGX41gmMFrEoBoYAWiFkGzvaBi2ZXLG/mVhCF4GcGpm/xhCsE/Yh/XKTup+gUlPFxv7mOCGkMGNOpDKn4O/Azu75IEzhJeGMeLNf9fLCMRh755Tdr8b//Az8p4OlkKVz3IGiVd2syZ9ZpYEz1XzsGtCMs0cAciI9dE9bkMv3SMMtmtsAzr/YWX7RXLWzRP/WWMQSZN5eTkQzByldqg89zweRq6zRdLtvt6+vb23Z7uUzT+/v1qudrHzzreNTMCcMycSbZ0N7t6CnzxgQG3B+POIZmo+0nhPeF++fn3a4qk4ouyTSh+593VpYiGOvz5meEq9oRf4mv5UZ4aeZ5O5JW78GNz2lRSyEZ1LxTnHBu/VfhRyFm7zkOU/sFmD38PIK3Rfi222l6fd1u396mCRgCR6z5IyKAPU37fcydiQgagNOkuKM0EvufTgSQOCqx4enpej0eef/8PE0sZjIl/P79eLxc/GeI87vFT+4npS5zRXLTpxyRHakggzIyx/WzKjfOWl9uWFL+22+xpVr18v3OgLL81sLLZ9TaM6vQc8TPUgnWKGBPF6fpej2dCOD1KviOx9PpcoFiYR3w7PdQMWx7fr5cACfW8Cwo5/EYj6stQI/rBPBywbnjiLgM99MTFJf3APPbN2jh5YK65M0Gz8bZSe94HgAQxzydzmfcY/tmw1fZbLhlZITrVnYjBKumHVLAfiywDcr00OvHENT68mNGg9G8Pn7sllq1aJPfo9aFauZgl64eT73V+GUEbxnjET3eTxMMMUDBF4//LhdAgGW/v1x+/OC23Q5I4bnH4273/o7HASJeH2vaAqi0bsfE2vs7VNUveB0Ch9v5jGdNEwy68NPztls7D+jj2xvAwzvAdgJbN7WrCjOX1iTHyCG/o/sz0ucCWHzcebIKO0cojGJ5Om2YmdBZ+o4fjmb96wWefbp8RNDPeqzB8HSC2T0e8fXhK4Y5Bmz46vF1Ajqu7fe45w1bqGhY55ZpYkCce3MLR5Vcx5qORMXT0XgPUAk7EDyfsQ3/A0AsOg/+DHh7e9vtoOGn026Hd8BnaI/crLLXGyZPzNUtOnsK+NnXCPlQQAaUK7/38Gux/i5SN48f0MNowGNnLnr0gOvRH8MdGcFq4m0NgviS4YJIg4TQ9UqXBF+01AtrVJmoWBjbYU+cGfc+/lx49OOvRcckgFLa93e75/F0ZKokr9qGNZ4HkeZ58Mejnw728MiOikHrAqW5GuE8Bvyy6wWr5ZBFf3pd0i1RXqn2VvEO/Oz6IfMKmPPEBF1E0GKAt+DHsRm0hKoCaIQIwRAIAA26hS34sl9fdzv+hfK8vjL3xvQTW+j7Yp2vw2Py6IdDDaBHEa9FE4wz4HnwjHge/PHwPIgtjlopYG5RtLxLQtUzxrzgrwDwpxdcz8QSPI+gPaYrpFvuMhv4W3NzixDVuRJtnVSFoNKsbjfCNKIYUcGgGYD4MvV1C8CXF33xQJa6yVHe9crZYr8Fx9c64cIxDe8aQDxHx3h/p69L9HAe+kngL0agPA+MSisAxwhWafpzChjHgF+mgFn7zOzaTEDtfnvH264o4gtRLHJorcA8fu3km4yxFPBW9TM3ZL/HFwi3ogJQJhjhEppcQIvH8MVjgXoqDHO5QPm0RY8SYAOQxrkPIB5VdFQKaNrI8zidcGQOExjRbAEc9cuvDHE/F6adDRnNBT8cQB9y9spnQFQNW6vmrLEIpVLA/iSPL0HSf/cqIA0YI4JZAWsn5PmZ5pqjMfi1NJbCV1uAn9YjgNcrQR4BeL3CNWGSau2EwPvlUeANewAvlzpDvULQz4uMvd+ogI+vzO4CmIEQcn382uvHKfxil3OweOCangcZwdoFEYJ+PmPkhnDsBwwjgHAuFP6Akebay8t+v9vxmTCL2E6Dy6Noy+Fg69RSwoXjY5GeeqdGo0PoMo0wPxULw/A8GILBAAKvieifB3CaxgDGlh/zyah128qv0b+fHVI9DizVtnrZpclIhC5e1Eah657nm4ejpnuGYFTAOg1r7Ib8+IG/UDP8hTmGIh0OGGsBIowQ4VLYGvaBDtLThZ4htMy98TzbYusMbOOYOD6MMLbh1XjPNUBEAw39A4Yqa8drwifmq8PzxjrPA+s8W9xjHQCOW3pWtXKVye0lpi4LQz/4Ul0a+AuDNfjZBJwQtO4pXv16PZKsLsMjWKvfWoNMpVRQR+quoyvfMFaG+ExrbT8cWD/H9bXpWjYzpDAMtJLzIjLFdbOjmLarS1nU106qG7eNG1W27Yq+1AnJXqghmC/WOf5wLRlHoRkLwuCmDNn+ZHVE8FH4eWPNajm/r5/zFVT0eCOCKnzCzYLm60uZ+LnAv6WBRutLVYzUTYGtfVB7SYl+rXDlFc8la3kFZGb0FwLo21REBJfh52sgFJ5RGNrmT3r4eZ0RfhzdPQrBfjxRaFmvrCrVlagKQe8o3ZKixTEf5oX1ubGtcKuA+Roo8bohfQTnYoMjBIl2rz/PpwBoH6hvd7HcAHv/VzMjsZXDXLJO9H1lLh+DXl3KFIE0BAVZO+r0CijFfkT7OCHIYqWeAlZ9BrMJrhC0JpbLx4G6eshXaOCGeW0tgstrISzkHCvhPYLzSYpRAa1vS0+P7kewVUaO8mqnx6qPfYfB2wCs60bY2kO9tloNa3tG9xGsRpKjOeLYqojHv69L4woFtKkvQ1Af79zHrEsYZ/83lu4tfRveBaqNpr+/D8F8BK9xNYJ81PrS3IrguHQpG+K622qV2vZfc2eX4zAMAuGco/c/6GplIQY82JjgqnmKttpIjb7yZxhYs5vfp7mfHUatGJ3vuAigPX3V5OPMAoqlk8Xv7FQ49zRfflkjWB88Wkd5s7sen6i3qFtAhqD8dGcEVcwSrR9XT+1A0B7IaW/0LQgfUQXQ84+z6E+LMJ+PxHpcpTn3FZitihD0+Wo2I45n7KJoU62fNkrU8YsQRLnLKLbj+zLnJTarExLbhmrX2fjxJKuYdS0JqeBnp+TtgDa+5t2CY5YTe0cYI9gxjsSeivfYrI+zcl3wqQWMBH9j7LJt+/6AbjU3Z7WjhyN+nmsWcLzMM/T0VXpB8BjBzCUOjkMXIfgeP+/YvfVTBN/gt0MwozBYwW+NIO+ZwXw4mlxstICZhIO5X4RwtKRiZ8w5flIQnuMwjuC7mREba0aO2JaqmQPu2UGCTrgfwXkVhHe9cTIiEF61gKe/Y52HUtBGT6C1jCfO12bA30Fw795RqWuukOZ3MO33MKkTXk3GVW3gsGco4OH3afKSNEoOXD0LPsNP1xSPe/mLn5bKI6gy5CcI1jHkZy3+2ag0HeOX+YYZBK3G6h0VBcmFWRLiRdukNUHKMf0IFgAUvTdEECFT53zioHCRArdwc4TWgWDk7MXZWrHztUutoocqgnZjcdykUL3YTpH5PsqG+6PApx5GC1ooZi2fZ5VBYvzOi8oV+6f9hLa4rcnHfEK+iuh4zyRfIuY3F88WsNcK4pJXHvvNTthv6vwRF7xuT9Um1TzKiOKbgnJHcVqfKfLop+lE5ZIVD/Ygrl9N6//iTjfqmcb/7AfwD9m/dNmwHERXAAAAAElFTkSuQmCC\");\n  background-position: center;\n  background-size: contain;\n  background-repeat: no-repeat; }\n\n@media (min-width: 640px) and (min-height: 480px) {\n  .windowsShuttingDown {\n    background-size: cover; } }\n";
styleInject$1(css$D);

var Desktop = function (_Component) {
  inherits$1(Desktop, _Component);

  function Desktop() {
    classCallCheck$1(this, Desktop);
    return possibleConstructorReturn$1(this, (Desktop.__proto__ || Object.getPrototypeOf(Desktop)).apply(this, arguments));
  }

  createClass$1(Desktop, [{
    key: "componentDidMount",
    value: function componentDidMount() {
      if (window.innerWidth < 800) {
        this.context.toggleMobile(true);
      }
    }
  }, {
    key: "render",
    value: function render() {
      var context = this.context;

      return React__default.createElement(
        ProgramProvider,
        null,
        React__default.createElement(
          Theme,
          {
            className: cx("desktop screen", {
              desktopX2: context.scale === 2,
              desktopX1_5: context.scale === 1.5,
              notMobile: !context.isMobile,
              fullScreen: context.fullScreen
            })
          },
          React__default.createElement(Background, null),
          React__default.createElement(DesktopView, null),
          React__default.createElement(TaskBar$1, null),
          React__default.createElement(WindowManager, null),
          React__default.createElement(TaskManager, null),
          React__default.createElement(Settings, null),
          React__default.createElement(ShutDown, null),
          context.crt && React__default.createElement(CRTOverlay, null)
        )
      );
    }
  }]);
  return Desktop;
}(React.Component);

Desktop.contextType = SettingsContext;


var App$1 = function App() {
  return React__default.createElement(
    SettingsProvider,
    null,
    React__default.createElement(Desktop, null)
  );
};

module.exports = App$1;
//# sourceMappingURL=index.js.map
