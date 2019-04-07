import React, { Component } from "react";
import { WindowProgram } from "packard-belle";
import cx from "classnames";
import safeEval from "safe-eval";
import Window from "../tools/Window";
import { msDos16 } from "../../icons";
import "./_styles.scss";

export const buildMenu = props => [
  {
    title: "File",
    options: [
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props.id) }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const lineStart = "C:\\WINDOWNS>";

class JSDos extends Component {
  state = {
    value: "",
    content: []
  };
  input = React.createRef();

  focusInput = () => {
    this.input.current.focus();
  };
  onInputBlur = () => {
    console.log("of");
  };
  onInputChange = e => {
    this.setState({ value: e.target.value });
  };
  processEntry = e => {
    e.preventDefault();
    let response;
    try {
      response = safeEval(this.state.value) || "Err... check your console?";
    } catch (e) {
      if (this.state.content.length % 3) {
        response = "Maybe try some JavaScript?";
      } else {
        response = "Invalid command entered";
      }
    }
    this.setState(state => ({
      value: "",
      content: [...state.content, lineStart + state.value, response].filter(
        entry => entry
      )
    }));
  };

  render() {
    const { props } = this;
    return (
      <>
        <Window {...props} initialHeight={200} initialWidth={400}>
          {rnd => (
            <WindowProgram
              title="JS DOS Prompt"
              icon={msDos16}
              onClose={() => props.onClose(props.id)}
              onMinimize={() => props.onMinimize(props.id)}
              onRestore={rnd.restore}
              onMaximize={rnd.maximize}
              changingState={rnd.state.isDragging || rnd.state.isResizing}
              maximizeOnOpen={rnd.context.isMobile}
              className={cx("JSDos", { "Window--active": props.isActive })}
              menuOptions={buildMenu(props)}
            >
              <form name="hiddenForm" onSubmit={this.processEntry}>
                <input
                  type="text"
                  value={this.state.value}
                  ref={this.input}
                  onChange={this.onInputChange}
                  onBlur={this.onInputBlur}
                />
              </form>
              <div className="terminal" onClick={this.focusInput}>
                <div>Microsoft(R) Windows 98 </div>
                <div style={{ marginRight: "12px", marginBottom: "6px" }}>
                  (C)Copyright Microsoft Corp 1981-1999.
                </div>
                <div className="terminal__content">
                  {this.state.content.map(entry => (
                    <div>{entry}</div>
                  ))}
                  {lineStart}
                  <span>{this.state.value}</span>
                </div>
              </div>
            </WindowProgram>
          )}
        </Window>
      </>
    );
  }
}

export default JSDos;
