import React from "react";
import { WindowProgram } from "packard-belle";
import Window from "../tools/Window";
import cx from "classnames";
import { notepad16 } from "../../icons";
import styles from "./_styles.scss";

export const buildMenu = (props, state) => [
  {
    title: "File",
    options: [
      {
        title: "New",
        isDisabled: !props.multiWindow && !props.onOpen,
        onClick: () => props.onOpen(props.id)
      },
      {
        title: "Open",
        isDisabled: true,
        onClick: () => props.onOpen(props.id)
      },
      { title: "Close", onClick: () => props.onClose(props.id) },
      {
        title: "Wrap",
        onClick: () => state.toggleWrap(!state.wrap),
        isChecked: state.wrap
      }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

class Notepad extends React.Component {
  static defaultProps = {
    data: {
      content: ""
    }
  };

  state = this.props.data
    ? {
        text: this.props.data.content,
        wrap: this.props.data.wrap
      }
    : {};

  toggleWrap = val => this.setState({ wrap: val });
  setText = text => this.setState({ text });

  render() {
    const { props, toggleWrap, setText } = this;
    const { wrap, text } = this.state;
    return (
      <Window
        {...props}
        icon={notepad16}
        footer={[
          { text: "needs 100% width height" },
          { text: "overflow control" }
        ]}
        menuOptions={buildMenu(props, { toggleWrap, wrap })}
        className={cx(styles.Notepad, props.className, {
          "Notepad--wrap": wrap
        })}
        title={`${
          props.title !== "Notepad" ? props.title : "Untitled"
        } - Notepad`}
        Component={WindowProgram}
      >
        <div className={styles.Notepad__textarea}>
          <textarea onChange={e => setText(e.target.value)}>{text}</textarea>
        </div>
      </Window>
    );
  }
}

export default Notepad;
