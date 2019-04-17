import React, { Component } from "react";
import { WindowProgram } from "packard-belle";
import cx from "classnames";
import safeEval from "safe-eval";
import Window from "../tools/Window";
import { msDos16 } from "../../icons";
import styles from "./_styles.scss";

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
      response =
        safeEval(this.state.value) ||
        "Err... if nothing happened then maybe check your console?";
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
      <Window
        {...props}
        title="JS DOS Prompt"
        icon={msDos16}
        menuOptions={buildMenu(props)}
        Component={WindowProgram}
        initialHeight={200}
        initialWidth={400}
        className={cx(styles.JSDos, props.className)}
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
        <div className={styles.terminal} onClick={this.focusInput}>
          <div>Microsoft(R) Windows 98 </div>
          <div style={{ marginLeft: "12px", marginBottom: "6px" }}>
            (C)Copyright Microsoft Corp 1981-1999.
          </div>
          <div className={styles.terminal__content}>
            {this.state.content.map(entry => (
              <div>{entry}</div>
            ))}
            {lineStart}
            <span>{this.state.value}</span>
          </div>
        </div>
      </Window>
    );
  }
}

export default JSDos;
